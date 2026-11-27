"""The Lean libraries declared in `lakefile.toml`, and the one coverage rule:
every local Lean source file is imported from some library's root.

`lake build` builds only the default library. The foundation gate builds and
audits every library except those listed in `CHECKED_ELSEWHERE`, which have
their own check because they are expensive.
"""
import re
import tomllib
from pathlib import Path

IMPORT = re.compile(r'^\s*(?:public\s+)?import\s+(\S+)', re.M)
DEFAULT = 'Pinwheel'
CHECKED_ELSEWHERE = {'PinwheelWitness': 'scripts/check-witness.py'}


def libraries(root):
    """`[(name, roots)]` in lakefile order; the default library comes first."""
    data = tomllib.loads((Path(root) / 'lakefile.toml').read_text())
    result = []
    for library in data.get('lean_lib', []):
        extra = set(library) - {'name', 'roots'}
        if extra:
            # srcDir or globs would change which files a library owns.
            raise RuntimeError(f"Unsupported lean_lib keys for {library['name']}: {sorted(extra)}")
        result.append((library['name'], list(library.get('roots', [library['name']]))))
    if not result or result[0][0] != DEFAULT:
        raise RuntimeError(f'The first declared library must be {DEFAULT}')
    unknown = set(CHECKED_ELSEWHERE) - {name for name, _ in result}
    if unknown:
        raise RuntimeError(f'Separately checked libraries are not declared: {sorted(unknown)}')
    return result


def gated(libs):
    """The libraries the foundation gate builds and audits."""
    return [(name, roots) for name, roots in libs if name not in CHECKED_ELSEWHERE]


def source_modules(root, libs):
    """Every local Lean source: each library's root files and the files under
    the directory named after a library."""
    root = Path(root)
    modules = {}
    for name, roots in libs:
        for module in roots:
            path = root / (module.replace('.', '/') + '.lean')
            if not path.is_file():
                raise RuntimeError(f'Missing root {module} of library {name}')
            modules[module] = path
        directory = root / name
        if directory.is_dir():
            for path in directory.rglob('*.lean'):
                modules['.'.join(path.relative_to(root).with_suffix('').parts)] = path
    return modules


def ordered_modules(libs, modules):
    """Local modules reachable from the libraries' roots, each once, with every
    module after its local imports; cycles are rejected."""
    ordered, active, seen = [], set(), set()
    def visit(name):
        if name in seen or name not in modules:
            return
        if name in active:
            raise RuntimeError('Cyclic local Lean imports: ' + name)
        active.add(name)
        for child in IMPORT.findall(modules[name].read_text()):
            visit(child)
        active.remove(name)
        seen.add(name)
        ordered.append((name, modules[name]))
    for _, roots in libs:
        for module in roots:
            visit(module)
    return ordered


def check_coverage(root):
    """Reject any local Lean file that no declared library imports."""
    libs = libraries(root)
    modules = source_modules(root, libs)
    reached = {name for name, _ in ordered_modules(libs, modules)}
    missing = sorted(set(modules) - reached)
    if missing:
        raise RuntimeError(f'Lean files outside every declared library ({len(missing)}): {missing}')
    return libs, modules


def audit_source(text, libs):
    """The whole-library audit text with each non-default library also imported."""
    if '\nimport Pinwheel\n' not in '\n' + text:
        raise RuntimeError('The audit no longer imports Pinwheel')
    extra = ''.join(f'import {module}\n' for name, roots in libs if name != DEFAULT for module in roots)
    return ('\n' + text).replace('\nimport Pinwheel\n', '\nimport Pinwheel\n' + extra, 1)[1:]
