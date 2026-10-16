# Fresh STA for the single hold-delay placement candidate

The timing helper is fixed and verified. Three fresh control evaluations reproduced the retained reference; three fresh candidate evaluations completed with zero setup and hold failures. Independent current-source, route and ownership reviews passed. This timing-only study completes inside its separate25-minute cap.

The helper uses typed immutable argument fields, explicit run deadlines tied to the frozen selection, exact five-view native versus nine-view STA library validation, unique-source custody checks, fresh output folders and a mandatory fresh computational control. Eighteen adverse host admission checks and two checks on actual saved inputs passed; independent review rejected five additional adverse cases. Fresh control STA provides the end-to-end evaluator verification. The prior arg-shadow failure, unlaunched late adapter and unpublished late publication configuration remain unchanged.

Global worst slack, ns:

| Corner | Control setup | Candidate setup | Control hold | Candidate hold |
|---|---:|---:|---:|---:|
| Typical | 5.67447000 | 5.67447000 | 0.10772700 | 0.10772700 |
| Slow | 0.00895284 | 0.00895284 | 0.26515900 | 0.26515900 |
| Fast, conditional | 9.06820000 | 9.06820000 | 0.01957480 | 0.01957480 |

Global margins match exactly. The slow setup limit is8.95284ps and fast hold limit19.5748ps. These remain below the stronger1ns slow setup and50ps global hold goals.

Target _30712_/D slack, ns:

| Corner | Control setup | Candidate setup | Control hold | Candidate hold |
|---|---:|---:|---:|---:|
| Typical | 15.065464 | 15.104321 | 0.446389 | 0.414917 |
| Slow | 14.530169 | 14.594338 | 0.815307 | 0.762891 |
| Fast, conditional | 15.356408 | 15.380548 | 0.245580 | 0.224905 |

The shorter local RC path increases setup reserve and consumes hold reserve. Slow endpoint setup improves64.169ps; fast endpoint hold decreases20.675ps to224.905ps, still above the50ps local floor.

Electrical violation blocks are byte-identical across each matched corner: slew2/7/2, fanout254 and capacitance0. The existing violations are still unresolved.

All six evaluations retain the exact saved canonical routes, netlists and NDR assignments. The producer’s one-cell move and three-unit Metal3 reduction2285 to2282 (total5230 to5227) remain source-bound; STA does not reroute or change placement. RTL, serial ABI, clock topology, library views and constraints stayed frozen. Protected507 and relevant historical evidence remain intact. No pin-access runtime workaround was needed in this STA-only evaluation.

Control and candidate primary runs took79.745 and81.538 seconds,161.283 seconds combined, sequentially at3CPUs/3GiB. Both actual owned labels were independently freshly queried absent. The final closeout binds full wall time including preparation, verification, measurement, cleanup, review and publication.

Qualification is estimated global-route RC. Fast uses -40C logic/IO and -55C SRAM. Annotation retains167 unannotated drivers; complete annotation, coupling/detailed vias, extracted timing, detailed routing, DRC/LVS and full signoff are not established here. The original failed native producer’s inherited power provenance remains unresolved. This is a qualified bounded comparison, with no candidate promotion, commit, PR or competition submission.

Evidence: [sealed results](../../physical/experiments/tt-buffered-hold30712-sta-results-01.json).
