"""Explicit local Python import closure for the physical producer snapshot."""
import ast
from pathlib import Path


def require(value, message):
    if not value: raise ValueError(message)


def dependency_closure(root, entries):
    root = Path(root).resolve(); pending = list(entries); files, external, dynamic = set(), set(), {}
    while pending:
        name = pending.pop(); path = root / name
        require(not Path(name).is_absolute() and '..' not in Path(name).parts and path.is_file() and
            not path.is_symlink() and path.resolve().is_relative_to(root), 'Invalid producer dependency: ' + name)
        if name in files: continue
        files.add(name)
        if path.suffix != '.py' or not name.startswith(('scripts/','physical/')): continue
        tree = ast.parse(path.read_bytes(), filename=name)
        targets = []
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Attribute) or node.func.attr not in ('spec_from_file_location','run_path'): continue
            arity, index = (2,1) if node.func.attr == 'spec_from_file_location' else (1,0)
            require(len(node.args) == arity and not node.keywords, 'Unresolved dynamic producer import: ' + name)
            value = node.args[index]
            if isinstance(value, ast.Call) and isinstance(value.func, ast.Name) and value.func.id == 'str' and len(value.args) == 1 and not value.keywords:
                value = value.args[0]
            if isinstance(value, ast.BinOp) and isinstance(value.left, ast.Name) and value.left.id == 'ROOT' and isinstance(value.op, ast.Div) and isinstance(value.right, ast.Constant) and type(value.right.value) is str:
                target = value.right.value
            elif isinstance(value, ast.Call) and isinstance(value.func, ast.Attribute) and value.func.attr == 'with_name' and len(value.args) == 1 and not value.keywords and isinstance(value.args[0], ast.Constant) and type(value.args[0].value) is str and isinstance(value.func.value, ast.Call) and isinstance(value.func.value.func, ast.Name) and value.func.value.func.id == 'Path' and len(value.func.value.args) == 1 and isinstance(value.func.value.args[0], ast.Name) and value.func.value.args[0].id == '__file__':
                require(Path(value.args[0].value).name == value.args[0].value, 'Escaping sibling producer import')
                target = str(Path(name).with_name(value.args[0].value))
            else: raise ValueError('Unresolved dynamic producer import: ' + name)
            require(target.startswith('scripts/') and target.endswith('.py') and '..' not in Path(target).parts,
                'Escaping dynamic producer import: ' + name)
            pending.append(target); targets.append(target)
        if targets: dynamic[name] = sorted(set(targets))
        for node in ast.walk(tree):
            modules = []
            if isinstance(node, ast.Import): modules = [alias.name for alias in node.names]
            if isinstance(node, ast.ImportFrom):
                require(node.level == 0, 'Relative producer imports require an explicit resolver')
                if node.module: modules = [node.module]
            if isinstance(node, ast.Call):
                call = node.func.id if isinstance(node.func, ast.Name) else node.func.attr if isinstance(node.func, ast.Attribute) else ''
                require(call not in ('__import__','import_module','SourceFileLoader') and
                    (call != 'exec_module' or targets),
                    'Dynamic producer import requires an explicit dependency: ' + name)
            for module in modules:
                local = root / 'scripts' / (module.replace('.', '/') + '.py')
                if local.is_file(): pending.append(str(local.relative_to(root)))
                else: external.add(module)
    return dict(files=sorted(files), external_imports=sorted(external), dynamic_imports=dynamic,
        boundary='Project imports are copied and hash sealed. Python standard library and pinned tool/runtime packages remain external runtime inputs.')


def stage_sources(root, destination, files, committed):
    root, destination = Path(root), Path(destination)
    require(not destination.exists(), 'Preserve prior physical producer snapshot')
    for name in files:
        source, target = root / name, destination / name
        data = committed(source)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        require(source.read_bytes() == data and target.read_bytes() == data, 'Producer changed during snapshot')
        target.chmod(0o444)
    return destination
