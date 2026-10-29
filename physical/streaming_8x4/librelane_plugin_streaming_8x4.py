"""New official8x4 flow from byte-identical certified prephysical logic."""
from librelane.flows import Flow
from librelane.flows.classic import Classic


@Flow.factory.register()
class Streaming8x4Certified(Classic):
    Steps = [step for step in Classic.Steps if step.id not in {
        'Yosys.Synthesis', 'Checker.YosysUnmappedCells',
        'Checker.YosysSynthChecks', 'Checker.NetlistAssignStatements',
    }]
