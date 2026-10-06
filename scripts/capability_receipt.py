"""Byte custody for local protocol gates and their fresh upload certificates."""
import hashlib
from pathlib import Path

from paired_execution import compile_e64
from paired_image_certificate import render
from validation_run import sha


class CapabilityEvidence:
    """Freeze consumed inputs before use and require unchanged bytes at closeout."""
    def __init__(self, root, out, sources, tools, models):
        self.root, self.out = Path(root), Path(out)
        self.source_sha256 = {str(Path(p).relative_to(self.root)): sha(p) for p in sources}
        self.tools_sha256 = {str(Path(p).relative_to(self.root)): sha(Path(p).resolve()) for p in tools}
        self.macro_models_sha256 = {Path(p).name: sha(p) for p in models}
        self.models = list(map(Path, models))
        self.generated_sha256, self.captured_inputs_sha256 = {}, {}
        self.image_certificates = []

    def capture(self, source, name):
        destination = self.out / name
        if destination.exists():
            raise FileExistsError('Preserve captured input: ' + str(destination))
        data = Path(source).read_bytes()
        destination.write_bytes(data)
        self.captured_inputs_sha256[name] = hashlib.sha256(data).hexdigest()
        return data

    def freeze_generated(self, path):
        path = Path(path)
        key = str(path.relative_to(self.out))
        if key in self.generated_sha256:
            raise ValueError('Generated artifact already frozen: ' + key)
        digest = sha(path)
        self.generated_sha256[key] = digest
        return digest

    def certify(self, name, source, run):
        from pinwheel_host import RESIDENT_FORMAT
        renderer, marker = render, 'Paired image certificate: kernel checked; standard axioms only.'
        compiler = compile_e64
        if getattr(source, 'image_format', None) == RESIDENT_FORMAT:
            from paired_execution import compile_resident
            from resident_image_certificate import render as resident_render, MARKER
            compiler, renderer, marker = compile_resident, resident_render, MARKER
        image = compiler(source.words, (source.idle_levels, source.idle_enabled), source.last)
        path = self.out / (name + '-certificate.lean')
        if path.exists():
            raise FileExistsError('Preserve upload certificate: ' + str(path))
        path.write_text(renderer(name.replace('-', '_'), source.words, source.last,
                               (source.idle_levels, source.idle_enabled), image, source.upload_words()))
        digest = self.freeze_generated(path)
        log = run(['lake', 'env', 'lean', '-DwarningAsError=true', path], name + '-certificate')
        if sha(path) != digest:
            raise RuntimeError('Certificate changed during kernel check: ' + path.name)
        if marker not in log:
            raise RuntimeError('Missing image certificate audit')
        self.image_certificates.append(dict(program=name, path=path.name, sha256=digest,
            populated_positions=source.last + 1, canonical_records=len(set(source.words))))

    def closeout(self):
        for name, digest in self.source_sha256.items():
            if sha(self.root / name) != digest:
                raise RuntimeError('Source changed during capability run: ' + name)
        for name, digest in self.tools_sha256.items():
            if sha((self.root / name).resolve()) != digest:
                raise RuntimeError('Tool changed during capability run: ' + name)
        for path in self.models:
            if sha(path) != self.macro_models_sha256[path.name]:
                raise RuntimeError('SRAM model changed during capability run: ' + path.name)
        for name, digest in self.generated_sha256.items():
            if sha(self.out / name) != digest:
                raise RuntimeError('Generated artifact changed after consumption: ' + name)
        for name, digest in self.captured_inputs_sha256.items():
            if sha(self.out / name) != digest:
                raise RuntimeError('Captured input changed after consumption: ' + name)

    def identity(self):
        return dict(source_sha256=self.source_sha256, tools_sha256=self.tools_sha256,
            macro_models_sha256=self.macro_models_sha256,
            generated_sha256=self.generated_sha256,
            captured_inputs_sha256=self.captured_inputs_sha256,
            image_certificates=self.image_certificates)
