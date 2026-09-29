// SPDX-License-Identifier: BSD-3-Clause
// Uses OpenROAD dcf36133 internals; see README.md for the deliberately narrow scope.
#include <algorithm>
#include <cmath>
#include <cstring>
#include <fstream>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
#include <tcl.h>
#include "grt/GlobalRouter.h"
#include "FastRoute.h"
#include "Grid.h"
#include "Net.h"
#include "ord/OpenRoad.hh"
namespace ord { grt::GlobalRouter* getGlobalRouter(); }
namespace grt {
class PinwheelRouteImport {
  GlobalRouter* r_ = nullptr;
  FastRouteCore* f_ = nullptr;
  bool active_ = false;
  std::map<std::string, GRoute> saved_;
  std::set<std::string> relaxed_;
  void require(bool yes, const std::string& why) {
    if (!yes) throw std::runtime_error(why);
  }
  odb::dbNet* net(const std::string& name) {
    require(active_, "No imported route session");
    auto* n = r_->block_->findNet(name.c_str());
    require(n != nullptr, "Missing net: " + name);
    return n;
  }
  int id(odb::dbNet* n) {
    auto it = f_->db_net_id_map_.find(n);
    require(it != f_->db_net_id_map_.end(), "Missing FastRoute net: " + n->getName());
    return it->second;
  }
  void syncOverflow() {
    f_->computeCongestionInformation();
    const auto& values=f_->getTotalOverflowPerLayer();
    f_->total_overflow_=std::accumulate(values.begin(),values.end(),0);
    bool overflow2d=false;
    for(int y=0;y<f_->y_grid_;++y) for(int x=0;x<f_->x_grid_;++x) {
      if(x<f_->x_grid_-1) overflow2d |= f_->graph2d_.getOverflowH(x,y)>0;
      if(y<f_->y_grid_-1) overflow2d |= f_->graph2d_.getOverflowV(x,y)>0;
    }
    f_->has_2D_overflow_=overflow2d;
  }
  // These are removable edge ledgers, not reconstructed Steiner topologies.
  // Every dirty net is cleared before native makeFastrouteNet/run rebuilds it.
  void reserve(odb::dbNet* n, const GRoute& route) {
    bool wires = false;
    for (const auto& s : route) wires |= !s.isVia();
    if (!wires && !f_->db_net_id_map_.count(n)) return;
    const int i = id(n);
    auto& tree = f_->sttrees_.at(i);
    require(tree.edges.empty(), "Refuse to double-reserve a net");
    for (const auto& s : route) {
      if (s.isVia()) continue;
      require(s.init_layer == s.final_layer, "Non-planar wire");
      int x = (s.init_x - f_->x_corner()) / f_->tile_size();
      int y = (s.init_y - f_->y_corner()) / f_->tile_size();
      const int xx = (s.final_x - f_->x_corner()) / f_->tile_size();
      const int yy = (s.final_y - f_->y_corner()) / f_->tile_size();
      const int l = s.init_layer - 1;
      require(std::min(x,xx)>=0 && std::max(x,xx)<f_->x_grid_
              && std::min(y,yy)>=0 && std::max(y,yy)<f_->y_grid_
              && l>=0 && l<f_->num_layers_ && (x==xx || y==yy), "Wire outside grid");
      if (x==xx && y==yy) continue;
      TreeEdge edge;
      edge.route.type = RouteType::MazeRoute;
      edge.route.grids.push_back({int16_t(x),int16_t(y),int16_t(l)});
      const int dx = (xx>x)-(xx<x), dy = (yy>y)-(yy<y);
      while (x!=xx || y!=yy) {
        x+=dx; y+=dy;
        edge.route.grids.push_back({int16_t(x),int16_t(y),int16_t(l)});
      }
      edge.route.routelen = edge.route.grids.size()-1;
      edge.len = edge.route.routelen;
      const auto a = edge.route.grids.front();
      f_->updateEdge2DAnd3DUsage(std::min(int(a.x),xx),std::min(int(a.y),yy),
                               std::max(int(a.x),xx),std::max(int(a.y),yy),l+1,1,n);
      tree.edges.push_back(std::move(edge));
    }
  }
 public:
  void start(const std::vector<std::string>& relaxed) {
    require(!active_, "Repeated import");
    r_=ord::getGlobalRouter(); f_=r_->fastroute_;
    require(!r_->initialized_ && r_->grouter_cbk_==nullptr, "Import requires fresh router");
    r_->setAllowCongestion(true);
    require(r_->haveRoutes(), "No saved route guides");
    require(!r_->haveDetailedRoutes(), "Detailed routes are outside this adapter");
    for (const auto& [n,route] : r_->routes_) saved_[n->getName()] = route;
    // Native initialization resets imported usage, and rebuilds all capacities
    // once. The retained route map is then replayed with effective NDR costs.
    r_->startIncremental();
    active_=true;
    for (const auto& name : relaxed) {
      require(relaxed_.insert(name).second, "Duplicate relaxed NDR net");
      auto* n=net(name);
      require(n->getNonDefaultRule()!=nullptr, "Relaxed net lacks persistent NDR");
      f_->setSoftNDR(id(n));
    }
    for (const auto& [n,route] : r_->routes_) reserve(n,route);
    syncOverflow();
    f_->clearNetsToRoute();
  }
  void snapshot(const std::string& path) {
    require(active_, "No imported route session");
    std::ofstream out(path, std::ios::out);
    require(bool(out), "Cannot write resource snapshot");
    out << "grid\t" << f_->x_grid_ << '\t' << f_->y_grid_ << '\t' << f_->num_layers_
        << '\t' << f_->x_corner() << '\t' << f_->y_corner() << '\t' << f_->tile_size() << '\n';
    for(int l=0;l<f_->num_layers_;++l) for(int y=0;y<f_->y_grid_;++y) for(int x=0;x<f_->x_grid_;++x) {
      for (int d=0;d<2;++d) {
        if ((d==0 && x==f_->x_grid_-1)||(d==1 && y==f_->y_grid_-1)) continue;
        const auto& e=d==0?f_->h_edges_3D_[l][y][x]:f_->v_edges_3D_[l][y][x];
        out << "3\t" << (d==0?'H':'V') << '\t' << l+1 << '\t' << x << '\t' << y
            << '\t' << e.cap << '\t' << e.red << '\t' << e.usage << '\n';
      }
    }
    auto& g=f_->graph2d_;
    for(int y=0;y<f_->y_grid_;++y) for(int x=0;x<f_->x_grid_;++x) {
      if(x<f_->x_grid_-1) out<<"2\tH\t0\t"<<x<<'\t'<<y<<'\t'<<g.getCapH(x,y)<<'\t'<<g.getUsageRedH(x,y)-g.getUsageH(x,y)<<'\t'<<g.getUsageH(x,y)<<'\n';
      if(y<f_->y_grid_-1) out<<"2\tV\t0\t"<<x<<'\t'<<y<<'\t'<<g.getCapV(x,y)<<'\t'<<g.getUsageRedV(x,y)-g.getUsageV(x,y)<<'\t'<<g.getUsageV(x,y)<<'\n';
    }
    std::map<std::string,FrNet*> nets;
    for(const auto& [n,i] : f_->db_net_id_map_) nets[n->getName()]=f_->nets_.at(i);
    for(const auto& [name,n] : nets) {
      out<<"net\t"<<name<<'\t'<<int(n->getEdgeCost())<<'\t'<<n->isSoftNDR();
      for(int l=0;l<f_->num_layers_;++l) out<<'\t'<<int(n->getLayerEdgeCost(l));
      out<<'\n';
    }
    require(bool(out), "Incomplete resource snapshot");
  }
  void release(const std::string& name) {
    auto* n=net(name); id(n);
    require(saved_.count(name), "Release regression requires a saved net");
    f_->clearNetRoute(n);
    syncOverflow();
  }
  void restore(const std::vector<std::string>& names) {
    // For edit/revert controls only. The caller first restores the actual
    // circuit and deletes temporary nets. Native invalidation releases new
    // routes; replay then adds only the original per-net demand.
    require(active_, "No imported route session");
    for(auto* n:r_->dirty_nets_) require(std::find(names.begin(),names.end(),n->getName())!=names.end(), "Undeclared dirty net during revert");
    f_->clearNetsToRoute();
    std::vector<Net*> dirty;
    r_->updateDirtyNets(dirty);
    for(const auto& name:names) {
      auto* n=net(name); require(saved_.count(name), "No saved route to restore");
      f_->clearNetRoute(n);
      r_->routes_[n]=saved_.at(name);
      reserve(n,r_->routes_.at(n));
    }
    syncOverflow();
    f_->clearNetsToRoute();
  }
  void route(const std::vector<std::string>& allowed) {
    require(active_ && !allowed.empty(), "No bounded edit to route");
    std::set<std::string> actual;
    for(auto* n:r_->dirty_nets_) {
      require(n->getSigType()==odb::dbSigType::SIGNAL && n->getNonDefaultRule()==nullptr,
              "Clock and NDR edits are outside this adapter");
      actual.insert(n->getName());
    }
    require(actual==std::set<std::string>(allowed.begin(),allowed.end()), "Dirty-net set differs from declared edit");
    f_->clearNetsToRoute();
    std::vector<Net*> dirty;
    r_->updateDirtyNets(dirty);
    require(dirty.size()==actual.size(), "Declared edit did not invalidate every route");
    r_->pad_pins_connections_.clear();
    int max_degree=1;
    for(auto* n:dirty) {
      require(!n->hasWires() && n->getNumPins()>1, "Unsupported dirty-net geometry");
      max_degree=std::max(max_degree,n->getNumPins());
      r_->makeFastrouteNet(n);
    }
    // Do not repeat global addResourcesForPinAccess for a fixed macro layout.
    f_->setMaxNetDegree(max_degree); f_->initAuxVar(); f_->setIncrementalGrt(true);
    const auto old_critical=f_->getCriticalNetsPercentage();
    f_->setCriticalNetsPercentage(0); f_->setCongestionReportIterStep(0);
    auto routes=r_->findRouting(dirty,r_->getMinRoutingLayer(),r_->getMaxRoutingLayer());
    require(routes.size()==actual.size(), "Missing rerouted net");
    r_->mergeResults(routes);
    f_->setCriticalNetsPercentage(old_critical); f_->setIncrementalGrt(false);
  }
  int overflow() {
    require(r_!=nullptr, "No imported router");
    return f_->totalOverflow();
  }
  void finish() {
    require(active_ && r_->dirty_nets_.empty(), "Unrouted edits remain");
    syncOverflow();
    r_->endIncremental(true);
    active_=false;
  }
};
} // namespace grt
static grt::PinwheelRouteImport session;
static int command(ClientData, Tcl_Interp* interp, int argc, Tcl_Obj* const argv[]) {
  try {
    if(argc<2) throw std::runtime_error("Expected import, snapshot, release, restore, route, or finish");
    const std::string cmd=Tcl_GetString(argv[1]);
    if(cmd=="overflow" && argc==2) {
      Tcl_SetObjResult(interp,Tcl_NewIntObj(session.overflow())); return TCL_OK;
    } else if(cmd=="finish" && argc==2) session.finish();
    else if((cmd=="snapshot" || cmd=="release") && argc==3) {
      if(cmd=="snapshot") session.snapshot(Tcl_GetString(argv[2])); else session.release(Tcl_GetString(argv[2]));
    } else if((cmd=="import" || cmd=="restore" || cmd=="route") && argc==3) {
      int n; Tcl_Obj** objects;
      if(Tcl_ListObjGetElements(interp,argv[2],&n,&objects)!=TCL_OK) return TCL_ERROR;
      std::vector<std::string> names; for(int i=0;i<n;++i) names.emplace_back(Tcl_GetString(objects[i]));
      if(cmd=="import") session.start(names);
      else if(cmd=="restore") session.restore(names);
      else session.route(names);
    } else throw std::runtime_error("Invalid route-import command arguments");
    return TCL_OK;
  } catch (const std::exception& e) {
    Tcl_SetObjResult(interp,Tcl_NewStringObj(e.what(),-1)); return TCL_ERROR;
  }
}
extern "C" int Pinwheelrouteimport_Init(Tcl_Interp* interp) {
  if(std::strcmp(ord::OpenRoad::getVersion(),"dcf36133a369abc8f3c5e5738cd4d82e4903c0e0")!=0) {
    Tcl_SetObjResult(interp,Tcl_NewStringObj("Unsupported OpenROAD revision",-1)); return TCL_ERROR;
  }
  Tcl_CreateObjCommand(interp,"pinwheel_route_import",command,nullptr,nullptr);
  return Tcl_PkgProvide(interp,"pinwheel_route_import","1.0");
}
