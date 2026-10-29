"""Portable consumer controls: compact inputs, never historical execution proof.

The exact technology LEF is required by the existing route-invariance reader;
its digest remains the production pin. Width declarations and the NDR witness
are the matching original input recipe. math-plan.json projects only the fixed
17-net geometry, R/via test coefficients and five via definitions from the
original consumer input plan; it omits execution/source-custody receipts. These
values exercise software arithmetic and parsing, not physical model accuracy.
retained-rules.txt is the exact unqualified input table required by the marker
transform hash gate. It is parameter data, not a solver execution capture.
Already tracked, authenticated DEF captures retain real writer serialization.
"""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'test/fixtures/streaming-8x4-consumer'
PINS = {'tech.lef': '3edd5a1ad31e8307be537d0d1b85c3258fefeb21aac04aaa476e4f72de4cffd5', 'ndr-witness.json': 'a8f66d50d82be6896fd89980b19d0d73c111ecf31adde2b09ac92f7aa3f5689a', 'retained-rules.txt': 'bf2af2235b102d7bb58fe782d8d8b41a64cb3efde46593562314a499e9c4a612', 'widths.lef': '5d0aefd5218dbfe8f2bac2406de7f18e4d45ccad255bbea75c9fde9e84c9b2e6', 'math-plan.json': '03644166ff8d8cd648aa18ca18ea512685458c8e11809ae2b01b2c955d157c4d'}


def read(name):
    raw = (FIXTURES / name).read_bytes()
    if hashlib.sha256(raw).hexdigest() != PINS[name]:
        raise ValueError('Portable consumer fixture bytes changed: ' + name)
    return raw.decode()


def tech(): return read('tech.lef')
def widths(): return read('widths.lef')
def rules(): return read('retained-rules.txt').encode()
def consumer_plan(): return json.loads(read('math-plan.json'))
def ndr_witness(): return json.loads(read('ndr-witness.json'))


def capture(which):
    return (ROOT / ('test/fixtures/streaming-8x4-rc-ndr-' + which + '-20261023.def')).read_text()


def original_def():
    # Remove the declaration block from the independently retained serialization,
    # without invoking the declaration writer that NDR controls test.
    text, count = re.subn(r'^NONDEFAULTRULES 2 ;\n.*?^END NONDEFAULTRULES\n', '', capture('before'), flags=re.M | re.S)
    if count != 1:
        raise ValueError('Expected one retained NDR declaration block')
    # The writer abbreviates repeated route coordinates as *. Expand those
    # exact coordinates for the original explicit-pair declaration test.
    previous = None
    def explicit(match):
        nonlocal previous
        pair = match.groups()
        if '*' in pair and previous is None:
            raise ValueError('Unanchored captured coordinate')
        previous = tuple(previous[i] if value == '*' else value for i, value in enumerate(pair))
        return '( ' + ' '.join(previous) + ' )'
    return re.sub(r'\(\s*(\*|-?\d+)\s+(\*|-?\d+)\s*\)', explicit, text)


def resource_record(root):
    # Exercise real seal verification with an actual source input in this fresh
    # checkout, rather than mocking the resource validator or loading a campaign.
    source = Path(__file__).resolve()
    return dict(argv=['fixture-worker', '--fixed-six-calls'],
        input_seals_required={str(source): hashlib.sha256(source.read_bytes()).hexdigest()},
        plan_path=str(root / 'synthetic-plan.json'), output_directory=str(root / 'synthetic-output'))


def count97_log():
    # Minimal protocol fixture for the intentional count-only terminal grammar.
    # This is not a captured solver run and confers no numerical success.
    return """Out-of-core free memory to link memory condition (-f): 1e+12
Mesh refinement (-m): 4.31745e-05
Solution scheme (-g): Galerkin, GMRES tolerance (-t): 0.0005
Potential interaction coefficient to mesh refinement ratio (-d): 0.25
Precond Type(s) (-p): Jacobi
Out-of-core temporary files folder: '/ooc-scratch/count97'
Number of panels after refinement: 47709
Number of links to be computed: 149944592
Error: available free memory is not enough to allocate any chunk
       Cannot go out-of-core, terminating process
Done computing links
Total time: 1.000000s (0 days, 0 hours, 0 mins, 1 s)
Error: Cannot go Out-of-Core (possibly disk full)!
"""
