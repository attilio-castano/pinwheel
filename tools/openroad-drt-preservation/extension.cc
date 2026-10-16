// SPDX-License-Identifier: BSD-3-Clause
// Pinned experimental entry adapter; native main/initDesign copies are generated.
#include <algorithm>
#include <cstdlib>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <tcl.h>
#include "drt/TritonRoute.h"
#include "db/obj/frShape.h"
#include "db/obj/frVia.h"
#include "db/tech/frConstraint.h"
#include "frDesign.h"
#include "global.h"
#include "io/io.h"
#include "odb/db.h"
#include "odb/dbShape.h"
#include "ord/OpenRoad.hh"

namespace ord { drt::TritonRoute* getTritonRoute(); }
namespace drt {
namespace {
using Rules = std::multiset<std::string>;
using Objects = std::map<std::string, Rules>;
void require(bool yes, const std::string& message) {
  if (!yes) throw std::runtime_error("Pinwheel preservation: " + message);
}
std::string quoted(const std::string& value) {
  std::string result = "\"";
  for (unsigned char c : value) {
    if (c == '\\' || c == '"') result += '\\';
    if (c < 32) result += "?"; else result += char(c);
  }
  return result + "\"";
}
std::string rectKey(const std::string& net, const std::string& layer, const odb::Rect& box) {
  std::ostringstream out;
  out << net << "|G|" << layer << '|' << box.xMin() << '|' << box.yMin() << '|' << box.xMax() << '|' << box.yMax();
  return out.str();
}
std::string viaKey(const std::string& net, const std::string& name, const odb::Point& origin) {
  return net + "|V|" + name + "|" + std::to_string(origin.x()) + "|" + std::to_string(origin.y());
}
std::string sourceRule(odb::dbTechNonDefaultRule* rule) {
  return rule == nullptr ? "DEFAULT" : "NDR:" + rule->getName();
}
std::string importedRule(frNet* net, bool tapered) {
  return net->getNondefaultRule() == nullptr || tapered ? "DEFAULT" : "NDR:" + net->getNondefaultRule()->getName();
}
size_t countObjects(const Objects& values) {
  size_t count = 0;
  for (const auto& [key, rules] : values) count += rules.size();
  return count;
}
}  // namespace

// Read-only audit runs immediately after import and before PA, GC, TA or DR.
void pinwheel_audit_import(odb::dbDatabase* db, frDesign* design) {
  const char* destination = std::getenv("PW_DRT_PRESERVATION_AUDIT");
  require(destination != nullptr && destination[0] != '\0', "audit destination is mandatory");
  require(!std::filesystem::exists(destination), "refuse to overwrite import audit");
  require(db && db->getChip() && db->getChip()->getBlock() && design && design->getTopBlock(), "imported design absent");
  Objects source, imported;
  size_t nets = 0, ndr_nets = 0, paths = 0, default_paths = 0, ndr_paths = 0;
  size_t segments = 0, vias = 0, patches = 0, tapered_segments = 0, tapered_vias = 0;
  for (auto net : db->getChip()->getBlock()->getNets()) {
    if (net->isSpecial() || net->getWire() == nullptr) continue;
    ++nets;
    ndr_nets += net->getNonDefaultRule() != nullptr;
    odb::dbWirePathItr iterator;
    iterator.begin(net->getWire());
    odb::dbWirePath path;
    while (iterator.getNextPath(path)) {
      ++paths;
      if (path.rule) ++ndr_paths; else ++default_paths;
      odb::dbWirePathShape shape;
      while (iterator.getNextShape(shape)) {
        const std::string rule = sourceRule(path.rule);
        if (shape.shape.isVia()) {
          const std::string name = shape.shape.getTechVia() ? shape.shape.getTechVia()->getName() : shape.shape.getVia()->getName();
          source[viaKey(net->getName(), name, shape.shape.getViaXY())].insert(rule);
        } else {
          source[rectKey(net->getName(), shape.shape.getTechLayer()->getName(), shape.shape.getBox())].insert(rule);
        }
      }
    }
    auto fr_net = design->getTopBlock()->findNet(net->getName());
    require(fr_net != nullptr, "source net unmatched in imported design: " + net->getName());
    for (auto& shape : fr_net->getShapes()) {
      require(shape->typeId() == frcPathSeg, "unsupported imported route shape");
      auto segment = static_cast<frPathSeg*>(shape.get());
      auto layer = design->getTech()->getLayer(segment->getLayerNum());
      imported[rectKey(net->getName(), layer->getName(), segment->getBBox())].insert(importedRule(fr_net, segment->isTapered()));
      ++segments;
      tapered_segments += segment->isTapered();
    }
    for (auto& via : fr_net->getVias()) {
      imported[viaKey(net->getName(), via->getViaDef()->getName(), via->getOrigin())].insert(importedRule(fr_net, via->isTapered()));
      ++vias;
      tapered_vias += via->isTapered();
    }
    for (auto& shape : fr_net->getPatchWires()) {
      require(shape->typeId() == frcPatchWire, "unsupported imported patch shape");
      auto patch = static_cast<frPatchWire*>(shape.get());
      auto layer = design->getTech()->getLayer(patch->getLayerNum());
      imported[rectKey(net->getName(), layer->getName(), patch->getBBox())].insert("DEFAULT");
      ++patches;
    }
  }
  std::vector<std::string> mismatches, ambiguities;
  for (const auto& [key, values] : source) {
    if (std::set<std::string>(values.begin(), values.end()).size() > 1) ambiguities.push_back(key);
    auto it = imported.find(key);
    if (it == imported.end() || it->second != values) mismatches.push_back(key);
  }
  for (const auto& [key, values] : imported) if (!source.count(key)) mismatches.push_back(key);
  const bool matched = nets > 0 && countObjects(source) > 0 && source == imported && ambiguities.empty();
  std::ofstream out(destination);
  require(bool(out), "cannot create import audit");
  out << "{\n  \"schema\": \"pinwheel-pre-GC-routing-import-v1\",\n"
      << "  \"status\": " << quoted(matched ? "passed" : "rejected") << ",\n"
      << "  \"revision\": \"dcf36133a369abc8f3c5e5738cd4d82e4903c0e0\",\n"
      << "  \"importer_variant\": " << quoted(PW_IMPORTER_PATCHED ? "patched" : "original") << ",\n"
      << "  \"before_PA_GC_TA_DR\": true,\n  \"audit_does_not_modify_imported_state\": true,\n"
      << "  \"source_routed_net_count\": " << nets << ",\n  \"source_NDR_net_count\": " << ndr_nets
      << ",\n  \"source_path_count\": " << paths << ",\n  \"source_default_path_count\": " << default_paths
      << ",\n  \"source_NDR_path_count\": " << ndr_paths << ",\n  \"source_object_count\": " << countObjects(source)
      << ",\n  \"imported_object_count\": " << countObjects(imported) << ",\n  \"imported_segment_count\": " << segments
      << ",\n  \"imported_via_count\": " << vias << ",\n  \"imported_patch_count\": " << patches
      << ",\n  \"imported_tapered_segment_count\": " << tapered_segments << ",\n  \"imported_tapered_via_count\": " << tapered_vias
      << ",\n  \"geometry_and_per_object_path_rule_multisets_exact\": " << (matched ? "true" : "false")
      << ",\n  \"mismatched_object_key_count\": " << mismatches.size() << ",\n  \"ambiguous_default_NDR_object_key_count\": " << ambiguities.size()
      << ",\n  \"first_mismatched_keys\": [";
  for (size_t i = 0; i < std::min<size_t>(10, mismatches.size()); ++i) out << (i ? ", " : "") << quoted(mismatches[i]);
  out << "]\n}\n";
  out.close();
  std::cout << "PINWHEEL_PRE_GC_IMPORT_AUDIT " << (matched ? "passed" : "rejected") << " nets=" << nets << " objects=" << countObjects(source) << " tapered_segments=" << tapered_segments << " tapered_vias=" << tapered_vias << std::endl;
  require(matched, "unmatched or ambiguous imported geometry/per-path rules before GC");
}

class PinwheelDRTPreservation {
 public:
  static void requireOrdinary(TritonRoute* router) {
    require(!router->distributed_, "distributed routing is outside this adapter");
  }
  static void roundtrip() {
    auto router = ord::getTritonRoute();
    requireOrdinary(router);
    require(router->getDesign()->getTopBlock() == nullptr, "roundtrip requires a fresh native router");
    router->initDesign();
    pinwheel_audit_import(router->db_, router->getDesign());
    io::Writer writer(router->getDesign(), router->getLogger());
    writer.updateDb(router->db_, router->getRouterConfiguration());
  }
};
}  // namespace drt

static int roundtrip(ClientData, Tcl_Interp* interp, int argc, Tcl_Obj* const argv[]) {
  if (argc != 1) { Tcl_WrongNumArgs(interp, 1, argv, ""); return TCL_ERROR; }
  try { drt::PinwheelDRTPreservation::roundtrip(); return TCL_OK; }
  catch (const std::exception& error) { Tcl_SetObjResult(interp, Tcl_NewStringObj(error.what(), -1)); return TCL_ERROR; }
}

static int detailedRoute(ClientData, Tcl_Interp* interp, int argc, Tcl_Obj* const argv[]) {
  if (argc != 21) { Tcl_WrongNumArgs(interp, 1, argv, "the identical twenty native detailed_route_cmd arguments"); return TCL_ERROR; }
  int via_gen, end_iter, seed, verbose, clean, no_pa, single_step, access, save, report_step;
  double k;
  if (Tcl_GetBooleanFromObj(interp, argv[6], &via_gen) != TCL_OK || Tcl_GetIntFromObj(interp, argv[7], &end_iter) != TCL_OK
      || Tcl_GetIntFromObj(interp, argv[11], &seed) != TCL_OK || Tcl_GetDoubleFromObj(interp, argv[12], &k) != TCL_OK
      || Tcl_GetIntFromObj(interp, argv[13], &verbose) != TCL_OK || Tcl_GetBooleanFromObj(interp, argv[14], &clean) != TCL_OK
      || Tcl_GetBooleanFromObj(interp, argv[15], &no_pa) != TCL_OK || Tcl_GetBooleanFromObj(interp, argv[16], &single_step) != TCL_OK
      || Tcl_GetIntFromObj(interp, argv[17], &access) != TCL_OK || Tcl_GetBooleanFromObj(interp, argv[18], &save) != TCL_OK
      || Tcl_GetIntFromObj(interp, argv[20], &report_step) != TCL_OK) return TCL_ERROR;
  try {
    if (single_step || no_pa || end_iter < 0 || end_iter > 50) throw std::runtime_error("Pinwheel preservation requires ordinary PA plus bounded full native strategy");
    auto* router = ord::getTritonRoute();
    drt::PinwheelDRTPreservation::requireOrdinary(router);
    if (router->getDesign()->getTopBlock() != nullptr) throw std::runtime_error("Pinwheel preservation requires a fresh native router");
    std::optional<int> report;
    if (report_step > 0) report = report_step;
    router->setParams({Tcl_GetString(argv[1]), Tcl_GetString(argv[2]), report,
                      Tcl_GetString(argv[3]), Tcl_GetString(argv[4]), Tcl_GetString(argv[5]),
                      bool(via_gen), end_iter, Tcl_GetString(argv[8]), Tcl_GetString(argv[9]), Tcl_GetString(argv[10]),
                      seed, k, verbose, bool(clean), !bool(no_pa), bool(single_step), access, bool(save), Tcl_GetString(argv[19]),
                      ord::OpenRoad::openRoad()->getThreadCount()});
    router->main();
    router->setDistributed(false);
    return TCL_OK;
  } catch (const std::exception& error) {
    Tcl_SetObjResult(interp, Tcl_NewStringObj(error.what(), -1)); return TCL_ERROR;
  }
}

extern "C" int Pinwheeldrtpreservation_Init(Tcl_Interp* interp) {
  if (std::string(ord::OpenRoad::getVersion()) != "dcf36133a369abc8f3c5e5738cd4d82e4903c0e0") {
    Tcl_SetObjResult(interp, Tcl_NewStringObj("Unsupported OpenROAD revision for preservation adapter", -1)); return TCL_ERROR;
  }
  Tcl_CreateObjCommand(interp, "pinwheel_drt_preservation_detailed_route_cmd", detailedRoute, nullptr, nullptr);
  Tcl_CreateObjCommand(interp, "pinwheel_drt_preservation_roundtrip", roundtrip, nullptr, nullptr);
  return Tcl_PkgProvide(interp, "pinwheel_drt_preservation", "1.0");
}
