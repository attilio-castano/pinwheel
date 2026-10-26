# Model24 fixed ideal end-face resistance control

This is a new 90-case consumer/reference experiment. No Native execution or
passing result is claimed by this preparation. The earlier R26 absolute gate
remains failed: 123 of 126 controls failed; its independent closeout SHA is
`9e4394463fb1a1ac7f12e53410826968a5cac35248bc59c4e3ccd165db57c7b4`.
The older 17-net experiment retains its 72 wire failures and 30 via passes.

The causal question is whether explicit conductor endpoints remove the earlier
software geometry mismatch without subtracting a measured intercept. Pinned
OpenROAD `dcf36133a369abc8f3c5e5738cd4d82e4903c0e0`
[`netRC.cpp`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/src/netRC.cpp#L354)
replaces the centerline distance with the shape bounding-box maximum dimension.
[`extmain.cpp`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/rcx/src/extmain.cpp#L357)
uses that length, shape width and LEF sheet resistance with `-lef_res`.
Default endpoint extensions add a wire width to a straight shape's length.
The retained R26 TYP M1 values fit that source policy; this does not repair or
relabel its failed centerline `Rsheet*L/W` gate.

The new fixed fixture declares explicit `POINT_EXT 0` at both endpoints.
[`definNet.cpp`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/src/defin/definNet.cpp#L317)
passes the extension to the wire encoder; the encoder preserves zero as an
explicit extension. The shape construction in
[`dbShape.h`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/include/odb/dbShape.h#L600)
then makes the straight conductor rectangle exactly length L and width W.
Positive-area BPin contacts lie outside that rectangle and touch each complete
transverse end face. The analytical reference is a uniform isotropic sheet
between ideal full end-face electrodes: `R = Rsheet * L / W`. It assumes ideal
electrodes and does not qualify finite-contact spreading, vias, bends, arbitrary
routes, process correlation or capacitance.

The fixed universe is five routing layers, preferred routing orientation,
default and double width, and lengths 50/100/150 µm, repeated for exact merged
ITF_MIN/TYP/MAX sheet resistances. Each corner uses an owned LEF with only its
five routing `RPERSQ` tokens changed. Every other original technology byte,
including named-via and cut-layer resistance, is restored and hash checked.
The unqualified retained TYP capacitance table remains a software dependency;
no capacitance value or corner accuracy is asserted.

Actual Native admission requires all 30 nets, 60 ports, five default widths and
directions, complete five-layer NDR, absence of cells/ITerms/special wires,
global BPin rectangles/layers/status/connectivity and explicit-zero route DEF.
Before/after DEF and Native TSV must be byte identical. Writer recentering is
accepted only when the exact global N-oriented BPin rectangle is unchanged.
The public
[`dbWire::getLength`](https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/odb/src/db/dbWire.cpp#L317)
additionally observes each zero-extension shape: its value must be `L-W`, as
`dbShape::getLength` is `abs(DX-DY)`. This quantity is an extent witness and is
never substituted for the analytical conductor length L. Exact Native API
compatibility remains an actual observation gate.

All 90 absolute resistance checks retain the 0.1% relative threshold. No
intercept fitting, subtraction, threshold change or numerical solver tuning is
included. A failed numeric corner can continue the predeclared three-call
packet; any geometry, resource or custody failure stops the suffix. Partial
packets cannot pass. Complete successful controls would support this ideal
reference and consumer policy only; all model/timing and general R/C/via
qualification flags remain false.

Preparation02 is under
`build/campaigns/8x4-20261024-01/model24-r-endpoint-preparation-02`:

| Packet | SHA-256 |
| --- | --- |
| Plan | `fc079452a9ca2abbea735a7e6fcc2e4fa654992c2fb16313689e1bb813994288` |
| Command proposal02 | `c92c90f6c4ffe15980474086a0cfa79971868329b71b60d5fdac7639f1628480` |
| HOST readiness02 | `4342499d041c89c58849a206a2cd7131f4c9696f09a7a4e3828ae0aa264055b7` |
| Launch/reopen02 | `77a9e039a0550ea61aea48ba6c595ae9dc1c7c3728973e3449a596eb33e1dd86` |
| Exact primary source intake | `5671eccd32df1d2407c26dac7f61bc6a9f86dcc932a222086a4107c7e90b03d8` |

Thirteen portable HOST controls pass normally and under `python3 -O`; they do not
invoke CAD or read ignored campaign fixtures. Preparation01 is preserved,
unexecuted and superseded after a HOST proposal exposed an image/interpreter
constant lookup on the legacy parser module. Preparation02 uses the reviewed
original cap-consumer runtime constants, with an added proposal control.
The cgroup contract control invokes the frozen dotted-key writer with mocked
literal kernel files, verifies this new R writer's explicit underscore
normalization, and feeds that actual owned schema through the new leaf reader.
The reader rejects a dotted-key receipt under the new R schema. No older writer
or executed receipt is changed by this schema check.

Only Root may execute the saved `resource_supervisor_argv`, after committing
the producers and creating its exact proposal-bound GO file. The fixed budget
is three 30-second Native leaves, 120 seconds whole worker, 180 seconds outer,
one CPU, 2 GiB, no extra swap and a 95% memory guard. The container has a
read-only root and inputs, no network and 128 MiB tmpfs; outputs are polled and
bounded. All 44 transitive producers, 22 prepared files, launcher, readiness,
proposal, plan and GO are explicit Root input seals. The saved
`HOST_closeout_argv` is eligible only after actual terminal cleanup and Root's
signal; it independently reopens the raw geometry, SPEF graph, numerical
comparison, complete source/input seals and shared lease cleanup.
