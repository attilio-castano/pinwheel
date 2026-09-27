// SPDX-License-Identifier: BSD-3-Clause
// The Resizer::repairHold adapter below is copied unchanged from OpenROAD
// dcf36133a369abc8f3c5e5738cd4d82e4903c0e0. Copyright (c) The OpenROAD Authors.
// This experimental Tcl entry point uses the existing resizer/hold objects.
#include <cmath>
#include <cstring>
#include <exception>
#include <tcl.h>
#include "RepairHold.hh"
#include "rsz/Resizer.hh"
#include "ord/OpenRoad.hh"
#include "utl/scope.h"
namespace ord {
rsz::Resizer* getResizer();
void ensureLinked();
}
namespace rsz {
bool Resizer::repairHold(
    double setup_margin,
    double hold_margin,
    bool allow_setup_violations,
    // Max buffer count as percent of design instance count.
    float max_buffer_percent,
    int max_passes,
    int max_iterations,
    bool match_cell_footprint,
    bool verbose)
{
  utl::SetAndRestore set_match_footprint(match_cell_footprint_,
                                         match_cell_footprint);
  // Some technologies such as nangate45 don't have delay cells. Hence,
  // until we have a better approach, it's better to consider clock buffers
  // for hold violation repairing as these buffers' delay may be slighty
  // higher and we'll need fewer insertions.
  // Obs: We need to clear the buffer list for the preamble to select
  // buffers again excluding the clock ones.
  utl::SetAndRestore set_exclude_clk_buffers(exclude_clock_buffers_, false);
  utl::SetAndRestore set_buffers(buffer_cells_, sta::LibertyCellSeq());

  resizePreamble();
  if (estimate_parasitics_->getParasiticsSrc()
          == est::ParasiticsSrc::global_routing
      || estimate_parasitics_->getParasiticsSrc()
             == est::ParasiticsSrc::detailed_routing) {
    opendp_->initMacrosAndGrid();
  }
  return repair_hold_->repairHold(setup_margin,
                                  hold_margin,
                                  allow_setup_violations,
                                  max_buffer_percent,
                                  max_passes,
                                  max_iterations,
                                  verbose);
}

}
static int repair(ClientData, Tcl_Interp* interp, int argc, Tcl_Obj* const argv[]) {
  if (argc != 9) {
    Tcl_WrongNumArgs(interp, 1, argv, "setup_seconds hold_seconds allow_setup max_buffer_fraction max_passes max_iterations match_footprint verbose");
    return TCL_ERROR;
  }
  double setup, hold, fraction;
  int allow, passes, iterations, match, verbose;
  if (Tcl_GetDoubleFromObj(interp, argv[1], &setup) != TCL_OK
      || Tcl_GetDoubleFromObj(interp, argv[2], &hold) != TCL_OK
      || Tcl_GetBooleanFromObj(interp, argv[3], &allow) != TCL_OK
      || Tcl_GetDoubleFromObj(interp, argv[4], &fraction) != TCL_OK
      || Tcl_GetIntFromObj(interp, argv[5], &passes) != TCL_OK
      || Tcl_GetIntFromObj(interp, argv[6], &iterations) != TCL_OK
      || Tcl_GetBooleanFromObj(interp, argv[7], &match) != TCL_OK
      || Tcl_GetBooleanFromObj(interp, argv[8], &verbose) != TCL_OK) return TCL_ERROR;
  if (!std::isfinite(setup) || !std::isfinite(hold) || !std::isfinite(fraction)
      || setup < 0 || hold < 0 || fraction < 0 || fraction > 1
      || passes <= 0 || iterations < -1) {
    Tcl_SetObjResult(interp, Tcl_NewStringObj("Invalid bounded hold-repair arguments", -1));
    return TCL_ERROR;
  }
  try {
    ord::ensureLinked();
    const bool changed = ord::getResizer()->repairHold(setup, hold, allow, fraction,
                                                      passes, iterations, match, verbose);
    Tcl_SetObjResult(interp, Tcl_NewBooleanObj(changed));
    return TCL_OK;
  } catch (const std::exception& error) {
    Tcl_SetObjResult(interp, Tcl_NewStringObj(error.what(), -1));
    return TCL_ERROR;
  }
}
extern "C" int Pinwheelhold_Init(Tcl_Interp* interp) {
  if (std::strcmp(ord::OpenRoad::getVersion(), "dcf36133a369abc8f3c5e5738cd4d82e4903c0e0") != 0) {
    Tcl_SetObjResult(interp, Tcl_NewStringObj("Unsupported OpenROAD revision for Pinwheel hold extension", -1));
    return TCL_ERROR;
  }
  Tcl_CreateObjCommand(interp, "pinwheel_repair_hold", repair, nullptr, nullptr);
  return Tcl_PkgProvide(interp, "pinwheel_hold", "1.0");
}
