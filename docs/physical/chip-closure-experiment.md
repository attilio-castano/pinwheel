# Chip protection and electrical integration

The September 27 continuation applies the [qualified fixture](live-closure-results.md)
to the exact saved third A layout. First qualify native initialization using
unchanged circuit/wire readbacks, complete pin membership, repair-path coverage
where needed, and repeatable detailed-wire resource accounting. Reject incomplete
state before invoking an edit that depends on it.

Build a declared positive-buffer candidate for the four overloaded branches and
one wire-capacitance failure. Prefer leaving all 97 existing antenna instances,
their input-net bindings, placements and the 340 clock nets unchanged. This is an
explicit preservation contract; numbered diode names and proximity do not prove
historical receiver ownership. Any changed branch must pass a fresh complete
antenna check after routing. Protect original placements and power geometry,
and connect new buffer power terminals.

Native repair is optional when an exact checked physical edit can express the
required change more narrowly. In either case, route the edited nets, extract new
parasitics, and require whole-network electrical and setup/hold checks in every
recorded corner. Verify actual netlist identity by known-buffer contraction and
retain negative controls. No stale SPEF acceptance or constraint relaxation.

Each local control/candidate invocation is bounded to 600 seconds, four CPUs and
6 GiB, one offline CAD process at a time. Reserve at most 1,800 CAD seconds for
this integration stage within the existing 28,800-second campaign, starting at
5,689.629 seconds. Record every failure and preserve all inputs and recipes.
This scope permits incremental detailed routing of the edited saved layout;
it does not allocate a fourth full-flow A attempt or claim final signoff.
The two B slots remain reserved behind accepted A.

Evidence lives under `build/validation/chip-closure-01/`. A successful candidate
must still retain all stated chip DRC/LVS, final extraction, power, fast-view and
formal-refinement gates before acceptance. Stop a nonconvergent local candidate
with its measurements and a causal next decision.
