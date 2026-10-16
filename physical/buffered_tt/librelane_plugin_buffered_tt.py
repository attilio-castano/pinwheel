"""Local experimental flow step; loaded only from a frozen buffered TT stage."""
from pathlib import Path
from librelane.steps import Step
from librelane.steps.odb import OdbpyStep
from librelane.steps.openroad import GlobalPlacement


@Step.factory.register()
class BufferedSramPower(OdbpyStep):
    id = 'Project.BufferedSramPower'
    name = 'Connect Exact Buffered SRAM Supply Columns'

    def get_script_path(self):
        return str(Path(__file__).with_name('connect_sram_power.py'))


@Step.factory.register()
class BufferedCapacityPlacement(GlobalPlacement):
    id = 'Project.BufferedCapacityPlacement'
    name = 'Place Buffered Engine With Native Routing Capacity Feedback'

    def get_script_path(self):
        return str(Path(__file__).with_name('gpl_capacity.tcl'))
