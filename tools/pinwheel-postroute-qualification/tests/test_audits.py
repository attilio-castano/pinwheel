import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from audits import annotation_audit, audit_spef, port_map


INV = {'instances': {'u': {'terminals': [['A', 'n', 'INPUT'], ['Z', None, 'OUTPUT']]}},
       'nets': {'n': {'sig_type': 'SIGNAL', 'ports': ['din'], 'terminals': [['u', 'A', 'INPUT']]}}}
SPEF = '''*SPEF "IEEE 1481-1998"
*DIVIDER /
*DELIMITER :
*BUS_DELIMITER [ ]
*C_UNIT 1 PF
*R_UNIT 1 OHM
*NAME_MAP
*1 n
*2 u
*3 din
*PORTS
*3 I
*D_NET *1 0.02
*CONN
*P *3 I *C 0 0
*I *2:A I *C 1 0
*CAP
1 *3 0.01
2 *2:A 0.01
*RES
1 *3 *1:1 1.5
2 *1:1 *2:A 2.5
*END
'''


class Audits(unittest.TestCase):
    def test_macro_345_port_map(self):
        cdl = ['VDD!', 'VDDARRAY!', 'VSS!'] + [f'A_DIN<{n}>' for n in range(342)]
        lef = [p.replace('<', '[').replace('>', ']') for p in cdl]
        self.assertEqual(len(port_map(cdl, lef)), 345)

    def test_macro_missing_port(self):
        with self.assertRaises(ValueError):
            port_map(['A<0>', 'VSS!'], ['A[0]'])

    def test_macro_alias(self):
        with self.assertRaises(ValueError):
            port_map(['A<0>', 'A[0]'], ['A[0]', 'A[1]'])

    def test_macro_rail_merging_rejected(self):
        with self.assertRaises(ValueError):
            port_map(['VDD!', 'VDDARRAY!', 'VSS!'], ['VPWR', 'VGND'])

    def test_SPEF_positive_full_coverage(self):
        result = audit_spef(SPEF, INV)
        self.assertEqual(result['status'], 'passed')
        self.assertEqual(result['expected_consumed_terminal_count'], 2)
        self.assertFalse(result['physical_connectivity_proven'])

    def test_SPEF_preserves_native_escaped_bus_names(self):
        inv = {'instances': INV['instances'], 'nets': {r'enabled\[0\]': INV['nets']['n']}}
        text = SPEF.replace('*1 n', r'*1 enabled\[0\]')
        self.assertEqual(audit_spef(text, inv)['status'], 'passed')

    def test_SPEF_missing_pin(self):
        result = audit_spef(SPEF.replace('*I *2:A I *C 1 0\n', ''), INV)
        self.assertEqual(result['status'], 'failed')
        self.assertEqual(result['connection_mismatches'][0]['missing'], [('I', 'u/A')])

    def test_SPEF_missing_network(self):
        result = audit_spef(SPEF[:SPEF.index('*D_NET')], INV)
        self.assertEqual(result['missing_networks'], ['n'])

    def test_SPEF_broken_resistor_graph(self):
        result = audit_spef(SPEF.replace('2 *1:1 *2:A 2.5', '2 *1:1 *1:2 2.5'), INV)
        self.assertEqual(result['status'], 'failed')
        self.assertEqual(result['resistance_graph_disconnections'][0]['unreachable_connection_nodes'], ['u:A'])

    def test_SPEF_nonfinite_negative_and_duplicate(self):
        for bad in (SPEF.replace('0.01', 'nan'), SPEF.replace('2.5', '-1'),
                    SPEF.replace('*3 din', '*3 din\n*3 another')):
            with self.assertRaises(ValueError):
                audit_spef(bad, INV)

    def test_SPEF_empty_parasitics_fail(self):
        result = audit_spef(SPEF[:SPEF.index('*RES')] + '*RES\n*END\n', INV)
        self.assertEqual(result['status'], 'failed')
        self.assertEqual(result['consumed_networks_without_RC_records'], ['n'])

    def test_annotation_zero_and_unused(self):
        self.assertEqual(annotation_audit('Found 0 unannotated drivers.\nFound 0 partially unannotated drivers.', INV)['status'], 'passed')
        self.assertEqual(annotation_audit('Found 1 unannotated drivers.\nu/Z\nFound 0 partially unannotated drivers.', INV)['status'], 'passed')

    def test_annotation_consumed_partial_unknown_fail(self):
        for text in ('Found 1 unannotated drivers.\ndin\nFound 0 partially unannotated drivers.',
                     'Found 0 unannotated drivers.\nFound 1 partially unannotated drivers.',
                     'Found 1 unannotated drivers.\nunknown\nFound 0 partially unannotated drivers.'):
            self.assertEqual(annotation_audit(text, INV)['status'], 'failed')

    def test_annotation_count_mismatch_rejected(self):
        with self.assertRaises(ValueError):
            annotation_audit('Found 2 unannotated drivers.\nu/Z\nFound 0 partially unannotated drivers.', INV)


if __name__ == '__main__':
    unittest.main()
