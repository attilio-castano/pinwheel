"""Compile only the standalone sink; never compile/copy DRT implementation."""
import hashlib
import json
from pathlib import Path
import subprocess

def command(reference, root):
    original = reference['commands'][1]['command']
    flags = original[:original.index('-DPW_IMPORTER_PATCHED=1')]
    flags = [v.replace('/work/diagnostic/', '/headers/') for v in flags]
    return flags + ['-fvisibility=hidden', str(root / 'observer.cc'), '-o', str(root / 'libpinwheel_logger_observer.so')]


def main():
    root = Path('/work/diagnostic')
    reference = json.loads(Path('/headers/native-05/build.json').read_text())
    flags = command(reference, root)
    process = subprocess.run(flags, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=240)
    (root / 'compile.log').write_text(process.stdout)
    record = {'status': 'passed' if process.returncode == 0 else 'failed', 'command': flags,
              'compiler_returncode': process.returncode, 'DRT_implementation_compiled': False}
    if process.returncode == 0:
        record['binary_sha256'] = hashlib.sha256((root / 'libpinwheel_logger_observer.so').read_bytes()).hexdigest()
    (root / 'build.json').write_text(json.dumps(record, indent=2) + '\n')
    assert process.returncode == 0, process.stdout[-5000:]


if __name__ == '__main__': main()
