// SPDX-License-Identifier: BSD-3-Clause
// Observer only. No routing implementation, setters, Writer or debug switches.
#include <atomic>
#include <cerrno>
#include <cmath>
#include <cstdio>
#include <fcntl.h>
#include <iomanip>
#include <memory>
#include <map>
#include <mutex>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
#include <unistd.h>
#include <sys/syscall.h>
#include <omp.h>
#include <tcl.h>
#include "drt/TritonRoute.h"
#include "db/obj/frAccess.h"
#include "db/obj/frInstTerm.h"
#include "frDesign.h"
#include "global.h"
#include "ord/OpenRoad.hh"
#include "spdlog/sinks/base_sink.h"
#include "utl/Logger.h"

namespace ord { drt::TritonRoute* getTritonRoute(); }
namespace pinwheel_logger_observer_v3 {
constexpr const char* revision = "dcf36133a369abc8f3c5e5738cd4d82e4903c0e0";
std::string q(const std::string& s) {
  std::ostringstream o; o << '"';
  for (unsigned char c : s) {
    if (c == '"' || c == '\\') o << '\\' << char(c);
    else if (c == '\n') o << "\\n";
    else if (c == '\r') o << "\\r";
    else if (c == '\t') o << "\\t";
    else if (c < 32) o << "\\u00" << std::hex << std::setw(2) << std::setfill('0') << int(c) << std::dec;
    else o << char(c);
  }
  o << '"'; return o.str();
}
std::string point(const odb::Point& p) { return "[" + std::to_string(p.x()) + "," + std::to_string(p.y()) + "]"; }
std::string rect(const odb::Rect& b) {
  return "[" + std::to_string(b.xMin()) + "," + std::to_string(b.yMin()) + "," + std::to_string(b.xMax()) + "," + std::to_string(b.yMax()) + "]";
}
const char* boolean(bool b) { return b ? "true" : "false"; }

class Sink final : public spdlog::sinks::base_sink<std::mutex> {
 public:
  Sink(drt::TritonRoute* router, const std::string& file, std::string inst, std::string term)
      : router_(router), inst_(std::move(inst)), term_(std::move(term)) {
    fd_ = ::open(file.c_str(), O_WRONLY | O_CREAT | O_EXCL, 0600);
    if (fd_ < 0) throw std::runtime_error("observer requires a new writable output");
    emit("{\"event\":\"installed\",\"revision\":" + q(revision) + ",\"target\":" + q(inst_ + "/" + term_) + "}");
  }
  ~Sink() override { if (fd_ >= 0) ::close(fd_); }
  void removed() { std::lock_guard<std::mutex> lock(mutex_); emit("{\"event\":\"removed\",\"io_ok\":" + std::string(boolean(io_ok_)) + "}"); }
  void fixture(bool enabled) { fixture_ = enabled; }
 private:
  struct Header { int iteration; double box[4]; };
  void emit(const std::string& s) noexcept {
    std::string line;
    try { line = s + "\n"; } catch (...) { io_ok_ = false; return; }
    const char* p = line.data(); size_t n = line.size();
    while (n) {
      const auto wrote = ::write(fd_, p, n);
      if (wrote < 0 && errno == EINTR) continue;
      if (wrote <= 0) { io_ok_ = false; return; }
      p += wrote; n -= size_t(wrote);
    }
  }
  std::string freshAPs(const Header& h) {
    const auto* design = router_->getDesign();
    if (!design || !design->getTopBlock() || !design->getTech()) throw std::runtime_error("fresh frDesign absent");
    const auto* inst = design->getTopBlock()->findInst(inst_);
    if (!inst) throw std::runtime_error("target frInst absent");
    const drt::frInstTerm* target = nullptr;
    for (const auto& t : inst->getInstTerms()) if (t->getTerm()->getName() == term_) target = t.get();
    if (!target) throw std::runtime_error("target frInstTerm absent");
    const auto idx = inst->getPinAccessIdx();
    const auto dbu = design->getTech()->getDBUPerUU();
    int b[4];
    for (int k = 0; k < 4; ++k) {
      const double scaled = h.box[k] * dbu;
      if (!std::isfinite(scaled) || std::abs(scaled - std::round(scaled)) > 1e-5) throw std::runtime_error("nonintegral worker box DBU");
      b[k] = int(std::llround(scaled));
    }
    const odb::Rect clip(b[0], b[1], b[2], b[3]);
    const auto shift = inst->getNoRotationTransform();
    const auto full = inst->getDBTransform();
    const auto& preferred = target->getAccessPoints();
    std::ostringstream out;
    out << "{\"source\":\"fresh_global_frDesign_inside_original_error_log_call\",\"dbu_per_micron\":" << dbu
        << ",\"route_box_dbu\":" << rect(clip) << ",\"instance\":" << q(inst_)
        << ",\"terminal\":" << q(term_) << ",\"net\":" << q(target->getNet() ? target->getNet()->getName() : "")
        << ",\"pin_access_idx\":" << idx << ",\"native_preferred_ap_count\":" << preferred.size()
        << ",\"pins\":[";
    int physical = 0, native = 0, eligible = 0, total = 0;
    for (const auto& pin : target->getTerm()->getPins()) {
      if (physical) out << ',';
      out << "{\"physical_pin_index\":" << physical++ << ",\"native_pin_index\":" << native
          << ",\"has_pin_access\":" << boolean(pin->hasPinAccess()) << ",\"pattern_count\":" << pin->getNumPinAccess()
          << ",\"shapes\":[";
      int shape = 0;
      for (const auto& fig : pin->getFigs()) {
        if (fig->typeId() != drt::frcRect && fig->typeId() != drt::frcPathSeg) throw std::runtime_error("unsupported target pin shape");
        const auto* s = static_cast<const drt::frShape*>(fig.get());
        auto box = s->getBBox(); const auto local = box; full.apply(box);
        if (shape++) out << ',';
        out << "{\"layer\":" << q(design->getTech()->getLayer(s->getLayerNum())->getName())
            << ",\"local_dbu\":" << rect(local) << ",\"global_dbu\":" << rect(box) << '}';
      }
      out << "],\"aps\":[";
      if (pin->hasPinAccess()) {
        if (idx < 0 || idx >= pin->getNumPinAccess() || size_t(native) >= preferred.size()) throw std::runtime_error("AP index outside native vectors");
        int number = 0;
        for (const auto& ap : pin->getPinAccess(idx)->getAccessPoints()) {
          auto global = ap->getPoint(); shift.apply(global);
          const bool inside = clip.intersects(global); total++; eligible += inside;
          if (number++) out << ',';
          out << "{\"local_dbu\":" << point(ap->getPoint()) << ",\"global_dbu\":" << point(global)
              << ",\"layer\":" << q(design->getTech()->getLayer(ap->getLayerNum())->getName())
              << ",\"preferred\":" << boolean(ap.get() == preferred[native]) << ",\"inside_route_box\":" << boolean(inside) << ",\"access\":[";
          int direction = 0; for (bool access : ap->getAccess()) { if (direction++) out << ','; out << boolean(access); }
          out << "]}";
        }
        native++; // Mirror native helper's continue-before-pinIdx++ behavior.
      }
      out << "]}";
    }
    out << "],\"generated_ap_count\":" << total << ",\"eligible_ap_count\":" << eligible
        << ",\"selected_truncated_endpoints_captured\":false}";
    return out.str();
  }
  std::string identity(size_t kernel, size_t raw) const {
    std::ostringstream out;
    out << "\"thread_id\":" << kernel << ",\"kernel_thread_id\":" << kernel
        << ",\"raw_msg_thread_id\":" << raw << ",\"cfg_max_threads\":" << router_->getRouterConfiguration()->MAX_THREADS
        << ",\"observer_omp_in_parallel\":" << boolean(omp_in_parallel())
        << ",\"observer_omp_team_size\":" << omp_get_num_threads()
        << ",\"observer_omp_thread_num\":" << omp_get_thread_num();
    return out.str();
  }
  void sink_it_(const spdlog::details::log_msg& msg) override {
    try {
      const auto kernel = ::syscall(SYS_gettid);
      if (kernel <= 0) throw std::runtime_error("Linux kernel caller thread ID unavailable");
      const auto caller = identity(size_t(kernel), msg.thread_id);
      const std::string payload(msg.payload.data(), msg.payload.size());
      std::smatch m;
      if (std::regex_search(payload, m, iteration_pattern_)) {
        iteration_ = std::stoi(m[1]);
        emit("{\"event\":\"iteration\",\"iteration\":" + std::to_string(iteration_) + "," + caller + "}");
      }
      if (payload.rfind("start DR worker (BOX)", 0) == 0) {
        Header h{iteration_, {0, 0, 0, 0}};
        if (std::sscanf(payload.c_str(), "start DR worker (BOX) ( %lf %lf ) ( %lf %lf )", &h.box[0], &h.box[1], &h.box[2], &h.box[3]) != 4) throw std::runtime_error("worker header parse failed");
        headers_[kernel] = h;
        std::ostringstream out; out << std::setprecision(17) << "{\"event\":\"worker\"," << caller << ",\"iteration\":" << iteration_ << ",\"route_box_um\":[" << h.box[0] << ',' << h.box[1] << ',' << h.box[2] << ',' << h.box[3] << "],\"payload\":" << q(payload) << '}'; emit(out.str());
      }
      if (payload.find("[ERROR DRT-1231]") != std::string::npos) {
        const auto header = headers_.find(kernel);
        const bool correlated = kernel != 0 && header != headers_.end() && header->second.iteration == iteration_;
        const bool target = payload.find("Pin " + inst_ + "/" + term_ + " does not have access point") != std::string::npos;
        std::ostringstream out; out << "{\"event\":\"DRT1231\"," << caller << ",\"iteration\":" << iteration_ << ",\"correlated\":" << boolean(correlated) << ",\"target_matches\":" << boolean(target) << ",\"fixture\":" << boolean(fixture_) << ",\"payload\":" << q(payload);
        try {
          if (!correlated || !target) throw std::runtime_error("no exact same-thread target header");
          if (!fixture_) { const auto aps = freshAPs(header->second); out << ",\"fresh_aps\":" << aps; }
        } catch (const std::exception& e) { out << ",\"capture_error\":" << q(e.what()); }
        out << '}'; emit(out.str());
      }
    } catch (...) { emit("{\"event\":\"observer_error\"}"); }
  }
  void flush_() override {} // Direct writes; never call the native Logger here.
  drt::TritonRoute* router_;
  std::string inst_, term_;
  int fd_{-1}, iteration_{-1}; bool io_ok_{true}, fixture_{false};
  const std::regex iteration_pattern_{R"(Start ([0-9]+)(st|nd|rd|th) .* iteration\.)"};
  std::map<size_t, Header> headers_;
};
std::shared_ptr<Sink> installed;
utl::Logger* installed_logger = nullptr;

int context(ClientData, Tcl_Interp* interp, int argc, Tcl_Obj* const argv[]) {
  if (argc != 1) { Tcl_WrongNumArgs(interp, 1, argv, ""); return TCL_ERROR; }
  auto* app = ord::OpenRoad::openRoad();
  auto* router = ord::getTritonRoute();
  if (!app || !router) return TCL_ERROR;
  std::ostringstream out;
  out << "{\"context\":\"current_Design_evalTclString_native_context\",\"openroad_pointer\":\"" << static_cast<const void*>(app)
      << "\",\"router_pointer\":\"" << static_cast<const void*>(router)
      << "\",\"openroad_thread_count\":" << app->getThreadCount()
      << ",\"cfg_max_threads\":" << router->getRouterConfiguration()->MAX_THREADS
      << ",\"kernel_thread_id\":" << ::syscall(SYS_gettid)
      << ",\"observer_omp_in_parallel\":" << boolean(omp_in_parallel())
      << ",\"observer_omp_team_size\":" << omp_get_num_threads()
      << ",\"observer_omp_thread_num\":" << omp_get_thread_num() << '}';
  Tcl_SetObjResult(interp, Tcl_NewStringObj(out.str().c_str(), -1)); return TCL_OK;
}
int install(ClientData, Tcl_Interp* interp, int argc, Tcl_Obj* const argv[]) {
  if (argc != 4) { Tcl_WrongNumArgs(interp, 1, argv, "new_output target_instance target_terminal"); return TCL_ERROR; }
  try {
    if (installed) throw std::runtime_error("observer already installed");
    auto* router = ord::getTritonRoute();
    if (!router || !router->getLogger()) throw std::runtime_error("native router/logger absent");
    auto sink = std::make_shared<Sink>(router, Tcl_GetString(argv[1]), Tcl_GetString(argv[2]), Tcl_GetString(argv[3]));
    router->getLogger()->addSink(sink); // Existing sinks retained; stock formatter remains %v.
    installed_logger = router->getLogger(); installed = std::move(sink);
    return TCL_OK;
  } catch (const std::exception& e) { Tcl_SetObjResult(interp, Tcl_NewStringObj(e.what(), -1)); return TCL_ERROR; }
}
int remove(ClientData, Tcl_Interp* interp, int argc, Tcl_Obj* const argv[]) {
  if (argc != 1) { Tcl_WrongNumArgs(interp, 1, argv, ""); return TCL_ERROR; }
  if (!installed || !installed_logger) { Tcl_SetObjResult(interp, Tcl_NewStringObj("observer not installed", -1)); return TCL_ERROR; }
  installed_logger->removeSink(installed); installed->removed(); installed.reset(); installed_logger = nullptr; return TCL_OK;
}
int fixture(ClientData, Tcl_Interp* interp, int argc, Tcl_Obj* const argv[]) {
  if (argc != 1 || !installed || !installed_logger) return TCL_ERROR;
  installed->fixture(true);
  std::atomic<int> threads{0}, caught{0}, wrong{0};
  auto* logger = installed_logger;
  logger->report("Start 0th optimization iteration.");
  #pragma omp parallel num_threads(4)
  {
    const int id = omp_get_thread_num(); threads++;
    logger->report("start DR worker (BOX) ( {} {} ) ( {} {} )", id * 10, 0, id * 10 + 1, 1);
    if (id == 2) {
      try { logger->error(utl::DRT, 1231, "Pin engine.memory.storage1/A_BM[31] does not have access point"); }
      catch (const std::runtime_error& e) { if (std::string(e.what()) == "DRT-1231") caught++; else wrong++; }
      catch (...) { wrong++; }
    }
  }
  installed->fixture(false);
  if (threads != 4 || caught != 1 || wrong != 0) { Tcl_SetObjResult(interp, Tcl_NewStringObj("native four-thread/error fixture failed", -1)); return TCL_ERROR; }
  Tcl_SetObjResult(interp, Tcl_NewStringObj("four_threads_original_DRT1231_exception_preserved", -1)); return TCL_OK;
}
} // namespace pinwheel_logger_observer_v3

extern "C" __attribute__((visibility("default"))) int Pinwheelloggerobserver_Init(Tcl_Interp* interp) {
  if (std::string(ord::OpenRoad::getVersion()) != pinwheel_logger_observer_v3::revision) return TCL_ERROR;
  Tcl_CreateObjCommand(interp, "pinwheel_logger_observer_install", pinwheel_logger_observer_v3::install, nullptr, nullptr);
  Tcl_CreateObjCommand(interp, "pinwheel_logger_observer_remove", pinwheel_logger_observer_v3::remove, nullptr, nullptr);
  Tcl_CreateObjCommand(interp, "pinwheel_logger_observer_context", pinwheel_logger_observer_v3::context, nullptr, nullptr);
  Tcl_CreateObjCommand(interp, "pinwheel_logger_observer_thread_fixture", pinwheel_logger_observer_v3::fixture, nullptr, nullptr);
  return Tcl_PkgProvide(interp, "pinwheel_logger_observer", "1.0");
}
