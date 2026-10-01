"""Conservative bundled compiler/runtime custody for the macOS protocol gate.

This fingerprints package files, not the OS dynamic loader, system libraries,
shell utilities, Python runtime or Lake/Lean runtime environment.
"""
import json
import os
from pathlib import Path
import re


ICARUS_SEEDS = (
    'bin/iverilog', 'bin/vvp',
    'libexec/realpath', 'libexec/iverilog', 'libexec/ivl', 'libexec/ivlpp', 'libexec/vvp',
    'lib/ivl/ivl', 'lib/ivl/ivlpp', 'lib/ivl/vvp.conf', 'lib/ivl/vvp-s.conf', 'lib/ivl/vvp.tgt',
    'lib/libvvp.1.14.0.dylib', 'lib/libbz2.1.0.8.dylib', 'lib/libz.1.3.2.dylib',
    'lib/libreadline.8.3.dylib', 'lib/libncurses.6.dylib',
)
VPI_NAMES = frozenset(('system.vpi', 'vhdl_sys.vpi', 'vhdl_textio.vpi',
                       'v2005_math.vpi', 'va_math.vpi', 'v2009.vpi'))
CIRCT_SEEDS = ('bin/circt-opt', 'lib/libCIRCTHW.dylib', 'lib/libMLIRIR.dylib')


class ProtocolToolClosure:
    """Require an unchanged conservative package inventory and indexed VPI loads."""
    def __init__(self, root, circt, iverilog, vvp, *, environment=None):
        self.root = Path(root)
        self.environment = os.environ if environment is None else environment
        self._check_environment()
        config = json.loads((self.root / 'tools/hardware-toolchain.json').read_text())
        if config['platform'] != 'darwin-arm64':
            raise RuntimeError('Protocol tool closure currently supports pinned darwin-arm64 packages')
        packages = config['packages']
        self.circt_root = self.root / 'build/tools' / packages['circt']['directory']
        self.icarus_root = self.root / 'build/tools' / packages['oss-cad-suite']['directory']
        if (Path(circt), Path(iverilog), Path(vvp)) != (self.circt_root / 'bin/circt-opt',
                self.icarus_root / 'bin/iverilog', self.icarus_root / 'bin/vvp'):
            raise RuntimeError('Compiler/runtime paths differ from the pinned package configuration')
        self.backend = self.icarus_root / 'lib/ivl'
        self.files = self._inventory()
        self.names = tuple(str(p.relative_to(self.root)) for p in self.files)
        self.vpi_modules = []

    def _check_environment(self):
        overrides = sorted(k for k, v in self.environment.items()
                           if v and (k.startswith('DYLD_') or k in
                                     ('IVERILOG_ICONFIG', 'IVERILOG_VPI_MODULE_PATH')))
        if overrides:
            raise RuntimeError('Refuse dynamic-loader environment overrides or compiler overrides: ' + ', '.join(overrides))

    def _inventory(self):
        groups = [(self.circt_root, CIRCT_SEEDS), (self.icarus_root, ICARUS_SEEDS)]
        files = set()
        for package, seeds in groups:
            for name in seeds:
                path = package / name
                if not path.is_file():
                    raise RuntimeError('Missing bundled tool dependency: ' + str(path))
                files.add(path)
            files.update((package / 'lib').glob('*.dylib'))
        files.update(p for p in self.backend.rglob('*') if p.is_file())
        for name in VPI_NAMES:
            path = self.backend / name
            if not path.is_file():
                raise RuntimeError('Missing bundled VPI dependency: ' + str(path))
            files.add(path)
        for path in files:
            package = self.circt_root if path.is_relative_to(self.circt_root) else self.icarus_root
            if not path.is_file() or not path.resolve().is_relative_to(package.resolve()):
                raise RuntimeError('Bundled tool dependency escapes its package: ' + str(path))
        return tuple(sorted(files))

    def check_executable(self, executable):
        """Check actual compiled VVP's absolute module references before runtime use."""
        modules = re.findall(r'^:vpi_module "([^"\n]+)";$', Path(executable).read_text(), re.MULTILINE)
        expected = {str(self.backend / name) for name in VPI_NAMES}
        if len(modules) != len(expected) or set(modules) != expected:
            raise RuntimeError('Compiled VVP does not load exactly the frozen bundled VPI modules')
        indexed = set(self.files)
        if any(Path(name) not in indexed for name in modules):
            raise RuntimeError('Compiled VVP references an unindexed VPI dependency')
        self.vpi_modules = sorted(str(Path(name).relative_to(self.root)) for name in modules)

    def closeout(self):
        self._check_environment()
        if tuple(str(p.relative_to(self.root)) for p in self._inventory()) != self.names:
            raise RuntimeError('Bundled tool dependency inventory changed during capability run')

    def identity(self):
        return dict(method='Conservative package inventory: explicit Icarus wrapper/compiler/runtime seeds, '
            'all lib/ivl assets, and all top-level bundled Icarus/CIRCT dylibs; each file hashed before use.',
            inventory_files=len(self.files), inventory_unchanged=True,
            compiler_backend=str(self.backend.relative_to(self.root)),
            vpi_modules=self.vpi_modules, loader_overrides_refused=True,
            compiler_config_and_vpi_path_overrides_refused=True,
            environment_boundary='OS dynamic loader and system libraries, shell utilities, Python runtime, '
                'and Lake/Lean runtime environment; Lean version separately recorded and checked.')
