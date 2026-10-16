"""Separate native process: real synchronous logger + four OpenMP threads."""
import hashlib
import json
import ctypes
import os
from pathlib import Path
from openroad import Tech, Design

root = Path('/work/diagnostic')
bindings = json.loads((root / 'bindings.json').read_text())
sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
assert sha('/proc/self/exe') == bindings['native_binary_sha256']
assert sha(root / 'libpinwheel_logger_observer.so') == bindings['observer_sha256']
tech = Tech(); design = Design(tech)
observer_handle = ctypes.CDLL(str(root / 'libpinwheel_logger_observer.so'), mode=os.RTLD_NOW | os.RTLD_GLOBAL)
design.evalTclString('load /work/diagnostic/libpinwheel_logger_observer.so Pinwheelloggerobserver')
design.evalTclString('pinwheel_logger_observer_install /work/diagnostic/observer.jsonl engine.memory.storage1 {A_BM[31]}')
result = design.evalTclString('pinwheel_logger_observer_thread_fixture')
assert result == 'four_threads_original_DRT1231_exception_preserved'
design.evalTclString('pinwheel_logger_observer_remove')
(root / 'fixture.json').write_text(json.dumps({'status': 'native_fixture_completed', 'original_exception_preserved': True,
    'actual_native_binary_sha256': sha('/proc/self/exe'), 'observer_sha256': bindings['observer_sha256'],
    'physical_design_loaded': False, 'fixture_is_not_a_physical_pin_access_failure': True}, indent=2) + '\n')
