import copy
import hashlib
import io
import json
from pathlib import Path
import struct
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import architecture_test_check as a

class DependencyCacheTests(unittest.TestCase):
    def test_interrupted_download_can_retry(self):
        class Interrupted(io.BytesIO):
            def read(self, size=-1):
                if self.tell():
                    raise OSError("interrupted")
                return super().read(size)

        payload = b"verified archive"
        entry = dict(filename="source.tar", url="https://example.invalid/source.tar",
                     sha256=hashlib.sha256(payload).hexdigest())
        with tempfile.TemporaryDirectory() as tmp, patch.object(a, "CACHE", Path(tmp)):
            with patch.object(a.urllib.request, "urlopen", side_effect=[Interrupted(b"partial"), io.BytesIO(payload)]):
                with self.assertRaisesRegex(OSError, "interrupted"):
                    a.ensure_archive(entry, True)
                self.assertEqual(list(Path(tmp).iterdir()), [])
                # A partial archive left by an older version can also be recovered.
                (Path(tmp) / entry["filename"]).write_bytes(b"partial")
                self.assertEqual(a.ensure_archive(entry, True).read_bytes(), payload)
                self.assertEqual(a.ensure_archive(entry, False).read_bytes(), payload)

    def test_interrupted_extraction_can_retry(self):
        def interrupt(tar, directory, **kwargs):
            tar.extract("source/file", directory, **kwargs)
            raise OSError("interrupted")

        with tempfile.TemporaryDirectory() as tmp, patch.object(a, "CACHE", Path(tmp)):
            archive = Path(tmp) / "source.tar"
            with tarfile.open(archive, "w") as tar:
                item = tarfile.TarInfo("source/file")
                item.size = 2
                tar.addfile(item, io.BytesIO(b"ok"))
            with patch.object(tarfile.TarFile, "extractall", interrupt):
                with self.assertRaisesRegex(OSError, "interrupted"):
                    a.ensure_extraction(archive, "source")
            self.assertFalse((Path(tmp) / "source").exists())
            a.ensure_extraction(archive, "source")
            self.assertEqual((Path(tmp) / "source/file").read_bytes(), b"ok")

class ArchitectureAdapterTests(unittest.TestCase):
    def setUp(self):
        self.rom=bytearray(a.ROM_SIZE);struct.pack_into('<I',self.rom,0,0x00100093)
        self.ram=bytes(a.RAM_SIZE)
        self.text='mem[X,0x000000000] -> 0x0093\nmem[X,0x000000002] -> 0x0010\n[0] [M]: 0x00000000 (0x00100093) addi x1,x0,1\nx1 <- 0x00000001\n\n'
    def parse(self,text=None):return a.parse_trace(self.text if text is None else text,4,[0]*33,self.rom,self.ram)
    def test_strict_valid_trace(self):
        frames,ram,reads=self.parse();self.assertEqual(frames[0]['registers'][1],1);self.assertEqual(ram,self.ram);self.assertEqual(reads,0)
    def test_complete_image(self):
        elf=a.complete_elf(self.rom,self.ram);rom,ram=a.elf_images(elf);self.assertEqual(rom,self.rom);self.assertEqual(ram,self.ram)
    def test_bad_elf_rejected(self):
        elf=bytearray(a.complete_elf(self.rom,self.ram));struct.pack_into('<I',elf,52+12,4)
        with self.assertRaises(ValueError):a.elf_images(elf)
    def test_unknown_trace_rejected(self):
        for text in (self.text+'garbage\n\n',self.text.replace('x1 <-','CSR 1 <-'),self.text.replace('[0]','[1]'),self.text[:-1],self.text.replace('0x00100093','0x00100013')):
            with self.subTest(text=text):
                with self.assertRaises(ValueError):self.parse(text)
    def test_boolean_aliases_rejected(self):
        frame=self.parse()[0][0]
        for key in ('pc','word','next_pc'):
            bad=copy.deepcopy(frame);bad[key]=False
            with self.assertRaises(ValueError):a.compare([bad],[frame])
        bad=copy.deepcopy(frame);bad['registers'][0]=False
        with self.assertRaises(ValueError):a.compare([bad],[frame])
    def test_partial_trace_rejected(self):
        frames=self.parse()[0]
        with self.assertRaises(ValueError):a.compare([],frames)
    def test_concrete_value_mismatch(self):
        frame=self.parse()[0][0];bad=copy.deepcopy(frame);bad['registers'][1]=2
        with self.assertRaises(RuntimeError):a.compare([bad],[frame])
    def test_memory_history_checked(self):
        text=self.text.rstrip()+'\nmem[R,0x001000000] -> 0x00000001\n\n'
        with self.assertRaises(ValueError):self.parse(text)
    def test_store_shape_rejected(self):
        frame=self.parse()[0][0]
        for store in ([a.RAM_BASE,True,0],[a.RAM_BASE,4,2**32],[0,4,0],[a.RAM_BASE+1,4,0]):
            bad=copy.deepcopy(frame);bad['write']=store
            with self.assertRaises(ValueError):a.validate_frame(bad)
    def test_read_value_and_x0_observation(self):
        frame=self.parse()[0][0];frame['read']=[a.RAM_BASE,1,0]
        a.validate_frame(frame)
        bad=copy.deepcopy(frame);bad['read'][0]+=1
        with self.assertRaises(RuntimeError):a.compare([bad],[frame])
        bad=copy.deepcopy(frame);bad['read'][1]=True
        with self.assertRaises(ValueError):a.compare([bad],[frame])
    def test_summary_types(self):
        summary=dict(cycles=3,data_completions=0,fetches=1,registers=[0]*32,retired=1,stop=4)
        a.validate_summary(summary)
        for key in ('cycles','data_completions','fetches','retired','stop'):
            bad=copy.deepcopy(summary);bad[key]=False
            with self.assertRaises(ValueError):a.validate_summary(bad)
    def test_single_instruction_mutation(self):
        elf=a.complete_elf(self.rom,self.ram);changed=a.patch_instruction(elf,0,0x40100093)
        self.assertEqual(a.elf_images(changed)[0][4:],self.rom[4:])
        self.assertEqual(a.elf_images(changed)[1],self.ram)
        with self.assertRaises(ValueError):a.patch_instruction(elf,a.RAM_BASE,0)
    def test_outside_ram_store_rejected(self):
        with self.assertRaises(ValueError):self.parse(self.text.rstrip()+'\nmem[W,0x000000000] <- 0x00000001\n\n')

if __name__=='__main__':unittest.main()
