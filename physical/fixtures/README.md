# Physical comparison fixtures

The [32-bit tile diagnostic](sram-tile/README.md) isolates a source/physical
resistor-width disagreement. Only an explicitly modified diagnostic passes;
the supplied tile remains unqualified. Its [study](../../docs/physical/sram-tile-results.md)
owns the evidence and source-contract gate.

The [hierarchical integration diagnostic](sram-integration/README.md) preserves
macro ports and array structure while locating the remaining failing contexts.

Use the [SRAM comparison policy](sram-comparison/README.md) for the qualified
local replay: four source layouts in both extraction modes, explicit physical
ports and deliberate defect controls. Its [study](../../docs/physical/sram-comparison-results.md)
owns the result and remaining macro-integration gate.

The [context fixture bundle](sram-context/README.md) is the frozen source input
to that experiment. Its original README and manifest used database matches as
native passes; the later study corrects six of those verdicts using the final
native port checks. Those historical files retain their identity-bearing bytes.
The current comparison recipe and results above supersede their pass claims.
