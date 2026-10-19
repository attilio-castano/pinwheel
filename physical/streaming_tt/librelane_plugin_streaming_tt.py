"""Physical flow starting from the exact certified mapped logical netlist.

Yosys.JsonHeader reads interface metadata only. No synthesis/FF optimization
step is allowed; physical transformations require a separate post-PNR proof.
"""
from librelane.flows import Flow
from librelane.flows.classic import Classic


@Flow.factory.register()
class StreamingTTCertified(Classic):
    Steps = [step for step in Classic.Steps if step.id not in {
        'Yosys.Synthesis', 'Checker.YosysUnmappedCells',
        'Checker.YosysSynthChecks', 'Checker.NetlistAssignStatements',
    }]
