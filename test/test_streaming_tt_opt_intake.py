"""Independent reimport identity and committed-archive refusal controls."""
from copy import deepcopy
import hashlib
import io
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_tt_opt_intake import named_connectivity,structural_connectivity,archive_membership,artifacts,restore_port_order
from streaming_mapped_netlist import parse_mapped
from streaming_mapped_liberty import parse_library
from test_streaming_mapped_netlist import fixture
from test_streaming_mapped_liberty import LIBRARY,TYPES


class ParentIntakeTests(unittest.TestCase):
    def test_port_order_restored_only_from_exact_actual_port_membership(self):
        original=fixture();candidate=deepcopy(original)
        ports=candidate['modules']['top']['ports']
        candidate['modules']['top']['ports']={name:ports[name] for name in reversed(ports)}
        restored=restore_port_order(candidate,original,'top')
        self.assertEqual(list(restored['modules']['top']['ports']),list(original['modules']['top']['ports']))
        self.assertEqual(restored,candidate)
        for fault in ('wire','extra','missing'):
            changed=deepcopy(original);other=changed['modules']['top']['ports']
            if fault=='wire':other['z']['bits'][0]='1'
            elif fault=='extra':other['extra']=deepcopy(other['z'])
            else:del other['z']
            with self.subTest(fault=fault),self.assertRaisesRegex(ValueError,'port values differ'):
                restore_port_order(candidate,changed,'top')
        changed=deepcopy(original)
        changed['modules']['top']['cells']['state']['connections']['D']=[2]
        with self.assertRaisesRegex(ValueError,'complete outer module differs'):
            restore_port_order(candidate,changed,'top')

    def test_wire_id_renumbering_preserves_exact_named_pin_identity(self):
        library=parse_library(LIBRARY,TYPES);original=fixture();renumbered=deepcopy(original)
        body=renumbered['modules']['top']
        for port in body['ports'].values():port['bits']=[value+1000 if type(value) is int else value for value in port['bits']]
        for cell in body['cells'].values():
            for pin,bits in cell['connections'].items():cell['connections'][pin]=[value+1000 if type(value) is int else value for value in bits]
        self.assertEqual(named_connectivity(parse_mapped(original,'top',library)),named_connectivity(parse_mapped(renumbered,'top',library)))

    def test_ff_d_output_or_cell_pin_fault_cannot_hide_behind_same_cell_inventory(self):
        library=parse_library(LIBRARY,TYPES);expected=named_connectivity(parse_mapped(fixture(),'top',library))
        for kind in ('d','output','pin'):
            changed=fixture();body=changed['modules']['top']
            if kind=='d':body['cells']['state']['connections']['D']=[2]
            elif kind=='output':body['ports']['z']['bits'][0]='1'
            else:body['cells']['combine']['connections']['A']=['1']
            with self.subTest(kind=kind):self.assertNotEqual(named_connectivity(parse_mapped(changed,'top',library)),expected)

    def test_missing_extra_modified_and_redirected_archive_members_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);path=root/'source.tar';expected={'source':hashlib.sha256(b'committed').hexdigest()}
            def make(entries):
                with tarfile.open(path,'w') as archive:
                    for name,data,kind in entries:
                        entry=tarfile.TarInfo(name)
                        if kind=='file':entry.size=len(data);archive.addfile(entry,io.BytesIO(data))
                        else:entry.type=tarfile.SYMTYPE;entry.linkname='outside';archive.addfile(entry)
            make([('source',b'committed','file')]);archive_membership(path,expected)
            for entries in ([],[('source',b'changed','file')],[('source',b'committed','file'),('extra',b'x','file')],
                    [('source',b'committed','file'),('source',b'committed','file')],[('../source',b'committed','file')],
                    [('source',b'','symlink')]):
                make(entries)
                with self.subTest(entries=entries),self.assertRaises(ValueError):archive_membership(path,expected)

    def test_generated_artifact_alias_cannot_replace_a_regular_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'proof.lean').write_text('actual source')
            self.assertEqual(set(artifacts(root)),{'proof.lean'})
            (root/'proof.olean').symlink_to('proof.lean')
            with self.assertRaisesRegex(ValueError,'Aliased'):artifacts(root)

    def test_relative_raw_and_absolute_optimized_receipts_keep_exact_membership(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp).resolve();proof=root/'proof.lean';proof.write_text('kernel source')
            receipt=root/'report.json';receipt.write_text('{}')
            digest=hashlib.sha256(proof.read_bytes()).hexdigest()
            self.assertEqual(artifacts(root,exclude=(receipt,)),{'proof.lean':digest})
            self.assertEqual(artifacts(root,exclude=(receipt,),absolute=True),{str(proof):digest})
            (root/'extra.olean').write_bytes(b'unrecorded')
            self.assertNotEqual(artifacts(root,exclude=(receipt,),absolute=True),{str(proof):digest})

    def test_actual_auto_cell_renaming_requires_semantic_state_and_all_pin_structures(self):
        library=parse_library(LIBRARY,TYPES);source=fixture();changed=deepcopy(source)
        changed['modules']['top']['cells']={name+'_renamed':value for name,value in changed['modules']['top']['cells'].items()}
        pool={};graph=parse_mapped(source,'top',library);other=parse_mapped(changed,'top',library)
        labels={next(iter(graph.state_bits)):('core','r_counter',0)}
        expected=structural_connectivity(graph,labels,pool)
        self.assertEqual(expected,structural_connectivity(other,labels,pool))
        self.assertNotEqual(named_connectivity(graph),named_connectivity(other))
        for kind in ('d','output','pin'):
            altered=deepcopy(changed);body=altered['modules']['top']
            if kind=='d':body['cells']['state_renamed']['connections']['D']=[2]
            elif kind=='output':body['ports']['z']['bits'][0]='1'
            else:body['cells']['combine_renamed']['connections']['A']=['1']
            with self.subTest(kind=kind):self.assertNotEqual(expected,structural_connectivity(parse_mapped(altered,'top',library),labels,pool))
        with self.assertRaisesRegex(ValueError,'structural state'):structural_connectivity(graph,{},pool)
        wrong={next(iter(graph.state_bits)):('core','r_other',0)}
        self.assertNotEqual(expected,structural_connectivity(other,wrong,pool))


if __name__=='__main__':unittest.main()
