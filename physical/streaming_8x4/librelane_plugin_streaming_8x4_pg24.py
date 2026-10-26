"""Bound PG-placement overlays around unchanged canonical OpenROAD bodies."""
from librelane.flows import Flow
from librelane.steps import Step
from librelane.steps import openroad
from librelane_plugin_streaming_8x4 import Streaming8x4Certified


class PGInitialDiodes(openroad._DiodeInsertion):
    def get_script_path(self): return '/work/closure/inputs/initial-pg.tcl'


class PGRepairAntennas(openroad.RepairAntennas):
    Steps = [PGInitialDiodes, openroad.CheckAntennas]


class PGDetailedRouting(openroad.DetailedRouting):
    def get_script_path(self): return '/work/closure/inputs/drt-pg.tcl'


@Step.factory.register()
class PGDiodeBootstrap(openroad.OpenROADStep):
    id = 'Pinwheel.PGDiodeBootstrap'
    name = 'PG-aware access for preserved antenna diodes'
    config_vars = openroad.DetailedRouting.config_vars
    def get_script_path(self): return '/work/closure/inputs/bootstrap.tcl'


def adapted(steps):
    result = []
    for step in steps:
        if step.id == 'OpenROAD.RepairAntennas': result.append(PGRepairAntennas)
        elif step.id == 'OpenROAD.DetailedRouting': result.extend((PGDiodeBootstrap, PGDetailedRouting))
        else: result.append(step)
    return result


@Flow.factory.register()
class Streaming8x4PGClosure24(Streaming8x4Certified):
    Steps = adapted(Streaming8x4Certified.Steps)
