"""First-use immutability, native command paths and incomplete-gate refusal."""
from copy import deepcopy
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_mapped_campaign import (Frozen, LABELS, Worker, acceptance, audit_source,
    read_json, validate_config, verify_qnames, verify_extra_qnames)


def config(root):
    return dict(root=str(root),library=str(root/'cells.lib'),tools={name:str(root/name) for name in ('lean','lake','yosys','abc')},
        components={name:dict(raw_json=str(root/(name+'.json')),sv=str(root/(name+'.sv'))) for name in LABELS})


def complete():
    return dict(components={name:dict(local_proofs_checked=True,full_component_checked=True,
        all_state_bijection=True,mutations_checked=True,whole_component_controls_checked=True,
        axiom_audit_checked=True,private_axiom_rejected=True) for name in LABELS},
        wrapper_checked=True,wrapper_axiom_audit_checked=True,wrapper_private_axiom_rejected=True,
        required_qnames_checked=True,extra_qnames_checked=True,frozen_inputs_unchanged=True)


class CampaignTests(unittest.TestCase):
    def test_first_hash_cannot_be_replaced_after_reuse_or_closeout(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'input';path.write_text('first');frozen=Frozen();frozen.add(path);original=dict(frozen.files)
            frozen.add(path);self.assertTrue(frozen.verify());path.write_text('changed')
            with self.assertRaisesRegex(ValueError,'before reuse'):frozen.add(path)
            self.assertEqual(frozen.files,original)
            with self.assertRaisesRegex(ValueError,'closeout'):frozen.verify()

    def test_missing_symlink_and_nonregular_inputs_refuse(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);target=root/'target';target.write_text('data');link=root/'link';link.symlink_to(target)
            for path in (root/'missing',root,link):
                with self.subTest(path=path),self.assertRaises(ValueError):Frozen().add(path)

    def test_every_component_wrapper_closure_and_private_control_is_mandatory(self):
        report=complete();self.assertTrue(acceptance(report))
        for label in LABELS:
            for flag in list(report['components'][label]):
                candidate=deepcopy(report);candidate['components'][label][flag]=False
                with self.subTest(label=label,flag=flag):self.assertFalse(acceptance(candidate))
        for flag in ('wrapper_checked','wrapper_axiom_audit_checked','wrapper_private_axiom_rejected','required_qnames_checked',
                'extra_qnames_checked','frozen_inputs_unchanged'):
            candidate=complete();candidate[flag]=False;self.assertFalse(acceptance(candidate))
        candidate=complete();candidate['error']='failed after work';self.assertFalse(acceptance(candidate))
        candidate=complete();del candidate['components']['frontend'];self.assertFalse(acceptance(candidate))

    def test_explicit_all_component_inputs_native_tools_and_timeout(self):
        with tempfile.TemporaryDirectory() as temporary:
            good=config(Path(temporary));self.assertIs(validate_config(good),good)
            for mode in ('missing-component','relative-source','relative-tool','timeout','name'):
                value=deepcopy(good)
                if mode=='missing-component':del value['components']['frontend']
                elif mode=='relative-source':value['components']['frontend']['raw_json']='relative.json'
                elif mode=='relative-tool':value['tools']['lean']='lean'
                elif mode=='timeout':value['timeout']=0
                else:value['components']['frontend']['raw_module']='Bad; import Arbitrary'
                with self.subTest(mode=mode),self.assertRaises(ValueError):validate_config(value)

    def test_fresh_directory_native_explicit_executable_and_precompile_freeze(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);out=root/'fresh';calls=[];holder={}
            def native(argv,label,timeout=None,reject=None):
                source=Path(argv[-1]);worker=holder['worker']
                self.assertIn(str(source),worker.frozen.files)
                self.assertEqual(argv[2],str(root/'lean'))
                self.assertIn('LEAN_PATH='+str(out),argv[1])
                self.assertGreater(timeout,0)
                Path(argv[argv.index('-o')+1]).write_bytes(b'captured native result')
                calls.append(label);return 'native output'
            worker=Worker(out,config(root),native);holder['worker']=worker
            worker.compile(out,'Good','example : True := by trivial\n')
            self.assertEqual(calls,['Good']);self.assertTrue(worker.frozen.verify())
            self.assertTrue(worker.report['commands'][0]['expected_outcome_completed'])
            with self.assertRaises(FileExistsError):Worker(out,config(root),native)
            with self.assertRaisesRegex(ValueError,'Preserve'):worker.compile(out,'Good','changed')

    def test_private_audit_selects_module_ownership_not_only_public_names(self):
        text=audit_source(['Good','PrivateFixture'])
        self.assertIn('getModuleIdxFor?',text)
        self.assertIn('"PrivateFixture"',text)
        self.assertIn('collectAxioms name',text)
        self.assertIn('let mut declarations : Nat := 0',text)
        self.assertIn('let mut theorems : Nat := 0',text)
        self.assertNotIn('text.startsWith "Pinwheel."',text)
        self.assertIn('run_cmd do',text)
        self.assertNotIn('#audit_mapped',text)

    def test_native_separate_audits_compose_and_aggregate_checks_new_private_owner(self):
        lean=shutil.which('lean')
        if lean is None:
            self.skipTest('Native Lean is unavailable for the composable audit regression')
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary)
            environment=dict(os.environ,LEAN_PATH=str(root))
            def compile_module(name,text,accepted=True):
                source=root/(name+'.lean');source.write_text(text)
                result=subprocess.run([lean,'--root='+str(root),'-DwarningAsError=true','-DmaxErrors=1',
                    '-o',str(root/(name+'.olean')),str(source)],cwd=Path(__file__).resolve().parents[1],
                    env=environment,capture_output=True,text=True,timeout=60)
                output=result.stdout+result.stderr
                if accepted:
                    self.assertEqual(result.returncode,0,name+': '+output)
                    self.assertTrue((root/(name+'.olean')).is_file())
                else:
                    self.assertNotEqual(result.returncode,0,name+': '+output)
                return output
            for suffix in ('A','B'):
                compile_module('MappedAuditFixture'+suffix,'namespace External'+suffix+'\n'
                    'private theorem hidden : (1 : Nat) = 1 := rfl\n'
                    'def wrapped : {n : Nat // n = 1} := ⟨1, hidden⟩\nend External'+suffix+'\n')
                output=compile_module('MappedAudit'+suffix,audit_source(['MappedAuditFixture'+suffix]))
                self.assertRegex(output,r'Mapped audit: [1-9]\d* declarations, [1-9]\d* theorems; standard axioms only\.')
            owners=['MappedAuditFixtureA','MappedAuditFixtureB','MappedAuditA','MappedAuditB']
            output=compile_module('MappedAuditAggregate',audit_source(owners))
            self.assertRegex(output,r'Mapped audit: [1-9]\d* declarations, [1-9]\d* theorems; standard axioms only\.')
            compile_module('MappedAuditNewPrivateOwner','namespace OutsidePinwheel\n'
                'private axiom neverUsed : False\nend OutsidePinwheel\n')
            output=compile_module('MappedAuditAggregatePrivateControl',
                audit_source([*owners,'MappedAuditAggregate','MappedAuditNewPrivateOwner']),accepted=False)
            self.assertIn('Unapproved axioms in',output)
            self.assertIn('neverUsed',output)
            self.assertNotIn('environment already contains',output)

    def test_all44_checked_qnames_are_unique_complete_and_untruncated(self):
        names=['Pinwheel.Test.target'+str(n) for n in range(44)]
        output='\n'.join(name+' (i : Nat) : True' for name in names)
        self.assertTrue(verify_qnames(output,names))
        for text,targets in [(output,names[:-1]),(output,names[:-1]+[names[0]]),
                (output.replace(names[-1]+' (',names[-1]+'Extra ('),names),
                (output+'\n'+names[0]+' : True',names)]:
            with self.assertRaises(ValueError):verify_qnames(text,targets)

    def test_six_extra_firstterminal_qnames_are_native_unique_and_separate(self):
        names=['Pinwheel.FirstTerminal.proof'+str(n)for n in range(6)]
        output='\n'.join(name+' : True'for name in names)
        self.assertTrue(verify_extra_qnames(output,names,['Pinwheel.Required.proof']))
        for targets,required,text in [(names[:-1],[],output),(names,[names[0]],output),
                (names,[],output.replace(names[-1]+' :',names[-1]+'Wrong :')),
                (names,[],output+'\n'+names[0]+' : True')]:
            with self.assertRaises(ValueError):verify_extra_qnames(text,targets,required)

    def test_duplicate_json_cannot_replace_an_input_manifest(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'config.json';path.write_text('{"components":{},"components":{}}')
            with self.assertRaisesRegex(ValueError,'Duplicate'):read_json(path)


if __name__=='__main__':unittest.main()
