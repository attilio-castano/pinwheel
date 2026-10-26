"""One separately authorized canonical post-antenna repair; original flow intact."""
from librelane.flows import Flow
from librelane.steps import Step
from librelane.steps.openroad import RepairDesignPostGRT
from librelane_plugin_streaming_8x4 import Streaming8x4Certified


@Step.factory.register()
class PostAntennaDesignRepair(RepairDesignPostGRT):
    id='OpenROAD.PostAntennaDesignRepair'
    name='Canonical Design Repair After Antenna Insertion'


def inserted(steps):
    result=[]
    for step in steps:
        result.append(step)
        if step.id=='OpenROAD.RepairAntennas':result.append(PostAntennaDesignRepair)
    return result


@Flow.factory.register()
class Streaming8x4PostAntennaRepair(Streaming8x4Certified):
    Steps=inserted(Streaming8x4Certified.Steps)
    gating_config_vars={**Streaming8x4Certified.gating_config_vars,
        'OpenROAD.PostAntennaDesignRepair':['RUN_POST_GRT_DESIGN_REPAIR']}
