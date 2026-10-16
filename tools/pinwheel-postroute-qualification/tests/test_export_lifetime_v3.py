import ast
from pathlib import Path
import unittest
import weakref

HERE = Path(__file__).resolve().parents[1]

class ExportLifetimeTest(unittest.TestCase):
    def execute_initialization(self, source):
        class Tech:
            pass
        class Design:
            def __init__(self, tech):
                self.tech = weakref.ref(tech)
            def readDb(self, path):
                if self.tech() is None:
                    raise RuntimeError("Tech owner destroyed before native readDb")
        nodes = []
        for node in ast.parse(source).body:
            if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id in ('tech', 'design') for t in node.targets):
                nodes.append(node)
            if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == 'readDb':
                nodes.append(ast.parse("design.readDb('fixture.odb')").body[0])
                break
        env = {'Tech': Tech, 'Design': Design}
        exec(compile(ast.fix_missing_locations(ast.Module(body=nodes, type_ignores=[])), '<lifetime-fixture>', 'exec'), env)
        return env

    def test_current_export_retains_tech_owner_through_readback(self):
        env = self.execute_initialization((HERE / 'export_native.py').read_text())
        self.assertIs(env['design'].tech(), env['tech'])

    def test_old_temporary_tech_pattern_is_detected(self):
        with self.assertRaisesRegex(RuntimeError, 'Tech owner destroyed'):
            self.execute_initialization("design = Design(Tech())\ndesign.readDb('fixture.odb')")

if __name__ == '__main__':
    unittest.main()
