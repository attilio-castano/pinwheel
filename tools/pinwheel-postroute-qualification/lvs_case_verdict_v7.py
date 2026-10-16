"""Finite, case-specific native Netgen evidence. No mismatch is a physical pass."""
import json
import re

UNIQUE = 'Circuits match uniquely.'
GRAPH_MISMATCH = {'Netlists do not match.', 'Netlists failed to match.', 'Circuits match with errors.'}
PIN_MISMATCH = 'Top level cell failed pin matching.'


def native_case_verdict(case, report, top, mutation):
    finals = re.findall(r'^Final result:\s*(.*?)\s*$', report, re.M)
    assert len(finals) == 1, 'Missing/ambiguous native comparison verdict'
    final = finals[0]
    assert final in GRAPH_MISMATCH | {UNIQUE, PIN_MISMATCH}, 'Unknown native comparison verdict'
    pins = top['pins']
    assert len(pins) == 2 and len(pins[0]) == len(pins[1])
    differences = [(a, b) for a, b in zip(*pins) if a != b]
    badnets = top.get('badnets', [])
    changes = mutation.get('changed_terminals', [])
    evidence = False
    mechanism = 'Unqualified native diagnostic shape; independent review required'
    if case == 'positive':
        evidence = final == UNIQUE and not differences and not badnets and not top.get('badelements', []) and not changes
        mechanism = 'Unique active-hierarchy native comparison with identical boundary pins'
    elif case in ('removed-terminal', 'bridged-nets'):
        encoded = json.dumps(badnets)
        required = ['net8042', 'net8046']
        if case == 'removed-terminal':
            required.append('PW_LVS_NEG_OPEN_30759_D')
        evidence = final in GRAPH_MISMATCH and bool(badnets) and all('"' + name + '"' in encoded for name in required)
        evidence = evidence and len(changes) == (1 if case == 'removed-terminal' else 2)
        mechanism = 'Declared standard-cell fault has native mismatched consumed-net graph'
    elif case == 'macro-detached-signal':
        expected = [('M0', '(no matching pin)'), ('(no pin)', 'M0')]
        evidence = (final == PIN_MISMATCH and differences == expected and not badnets and not top.get('badelements', [])
            and len(pins[0]) == 351 and len(changes) == 1
            and changes[0] == {'instance':'memory','pin':'A_ADDR[5]','before':'M0','after':'PW_LVS_NEG_MACRO_OPEN'})
        mechanism = 'Exact native M0 top-port mismatch from the one declared macro terminal detach'
    elif case == 'macro-bridged-signals':
        encoded = json.dumps(badnets)
        expected = [('M1', '(no matching pin)'), ('(no pin)', 'M1')]
        exact_fault = len(changes) == 1 and changes[0] == {'instance':'memory','pin':'A_ADDR[4]','before':'M1','after':'M0'}
        pin_evidence = final == PIN_MISMATCH and differences == expected and not badnets and not top.get('badelements', [])
        graph_evidence = final in GRAPH_MISMATCH and bool(badnets) and all('"' + name + '"' in encoded for name in ('M0', 'M1'))
        evidence = exact_fault and (pin_evidence or graph_evidence)
        mechanism = 'Exact macro M1-to-M0 terminal attachment fault with native targeted pin/net mismatch'
    elif case == 'macro-detached-VSS':
        encoded = json.dumps(badnets)
        exact_fault = len(changes) == 1 and changes[0] == {'instance':'memory','pin':'VSS!','before':'VGND','after':'PW_LVS_NEG_MACRO_VSS_OPEN'}
        evidence = (exact_fault and final in GRAPH_MISMATCH and bool(badnets)
            and all('"' + name + '"' in encoded for name in ('VGND', 'PW_LVS_NEG_MACRO_VSS_OPEN')))
        mechanism = 'Exact macro VSS attachment fault with native VGND/fresh-node mismatched graph'
    else:
        raise ValueError('Unsupported fixture case')
    return {'completed': True, 'match_uniquely': final == UNIQUE, 'native_final_result': final,
        'targeted_native_evidence_verified': bool(evidence), 'targeted_evidence_mechanism': mechanism,
        'native_top_pin_differences': differences, 'native_badnet_groups': len(badnets),
        'independent_semantic_review_required': True}
