# Native8x4 receipt serialization fixture

`probe01-staprepnr-state.json` is an exact, unmodified copy of the native
`04-openroad-staprepnr/state_out.json` produced by the first official8x4 probe
on 2026-10-22. Original campaign path:
`build/campaigns/8x4-20261022-01/native-probe-01/flow/04-openroad-staprepnr/state_out.json`.
SHA-256: `166a2f0e0e3a013fcd57c080f0cf6fd0307554d8c34c8e5143dc3c6acfbed7e9`.

The native file contains bare `Infinity` observations. The original native
flow finished, but its HOST receipt serialization failed because strict JSON
refused these values. The regression preserves those bytes and hashes while
requiring explicit diagnostic tags in the new HOST receipt. It grants no
timing, physical, proof or tapeout acceptance. The original failed receipt
and its resource closeout remain unchanged.
