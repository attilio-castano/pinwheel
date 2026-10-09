#!/usr/bin/env python3
"""Export a bounded source-to-resident SPI session for the design explorer.

The commands enter the unchanged SRAM controller ABI, rather than a simulated
serial packet frontend. The existing source engine and independent resolved-wire
peer provide each transfer's raw-input history. A fresh Lean replay advances the
actual typed SramModel and an independently evolved SharedBranches reference,
checks every core field and public output, then returns the recorded states.
The browser only replays those states. This finite executable witness is not a
universal compiler, serial delivery, RTL, electrical or physical-chip theorem.

Run from the repository root after the narrow imports are built:
  lake build Pinwheel.Hardware.Buffered.SramState Pinwheel.Hardware.Buffered.SramModel
  python3 -B scripts/ExplorerBufferedSession.py
"""
from dataclasses import asdict
import ast
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from buffered_counted_hardware import compact_spi, decode_control
from buffered_engine import BufferedEngine, BufferedWireSimulation
from buffered_peers import BufferedSPIPeer
from buffered_reactive_hardware import decode_reactive_instruction
from buffered_sram_hardware import FORMAT, BufferedSramHardwareImage, lower_sram
from pinwheel_buffers import TransferSlot

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'docs/explorer/buffered-session.json'

LEAN_WORKER = r'''import Pinwheel.Hardware.Buffered.SramModel
import Pinwheel.Hardware.Buffered.SramState
import Lean

open Pinwheel.Hardware Pinwheel.Hardware.Buffered

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError ("Buffered explorer replay: " ++ label))
private def get (j : Lean.Json) (key : String) : IO Lean.Json := IO.ofExcept (j.getObjVal? key)
private def number (j : Lean.Json) (key : String) : Nat :=
  ((j.getObjVal? key).bind Lean.Json.getNat?).toOption.getD 0
private def commandValues (j : Lean.Json) (raw : Nat) : Values Reactive.Input := fun {w} p =>
  BitVec.ofNat w (if Reactive.inputLabel p == "raw_inputs" then raw
    else number j (Reactive.inputLabel p))
private structure Reference where
  bank : Array Nat
private def Reference.values (s : Reference) : Values SharedBranches.Register := fun {w} r =>
  BitVec.ofNat w (s.bank[SharedBranches.registerIndex r]?.getD 0)
private def expressions : Array (Sigma (Expr Reactive.Input SharedBranches.Register)) :=
  SharedBranches.registers.map fun ⟨w,r⟩ => ⟨w,SharedBranches.circuit.next r⟩
private def Reference.step (s : Reference) (i : Values Reactive.Input) : Reference :=
  ⟨MemoEval.evalMany i s.values expressions⟩
private def physicalState (s : SramModel.State) : SramState.State :=
  ⟨s.registers.values, fun p => ⟨s.contents p, BitVec.ofNat 64 s.q[p.val]!⟩⟩

def main (args : List String) : IO Unit := do
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (args.headD "")))
  let vectors ← IO.ofExcept ((← get j "vectors").getArr?)
  let mut actual := SramModel.State.initial 17
  let mut reference : Reference := ⟨SharedBranches.registers.mapIdx fun k ⟨w,_⟩ =>
    (19*15485863 + k*32452843 + 49979687) % 2^w⟩
  let mut result : Array Lean.Json := #[]
  let mut coreChecks := 0
  let mut outputChecks := 0
  let mut residentChecks := 0
  let mut ordinaryBoundaries := 0
  let mut storageMutations := 0
  for edge in [:vectors.size] do
    let v := vectors[edge]!
    let command ← get v "command"
    let i : Values Reactive.Input := commandValues command (number v "raw_inputs")
    let after := actual.step i
    let expected := reference.step i
    for ⟨_,r⟩ in SharedBranches.registers do
      match r with
      | .core r =>
        check (after.registers.values (.core r) == expected.values (.core r))
          s!"core {Reactive.registerLabel r} at edge {edge}"
        coreChecks := coreChecks+1
      | _ => pure ()
    let mut state : List (String × Lean.Json) := []
    for ⟨_,o⟩ in Reactive.outputs do
      let label := Reactive.outputLabel o
      let observed := if label == "rejected" then actual.observe i o else after.observe i o
      let want := SharedBranches.circuit.observe i
        (if label == "rejected" then reference.values else expected.values) o
      check (observed == want) s!"output {label} at edge {edge}"
      state := state ++ [(label,Lean.toJson observed.toNat)]
      outputChecks := outputChecks+1
    if number command "initialize" == 1 || number command "command" == 2 ||
        number command "command" == 3 then
      let ordinary := (physicalState actual).step i
      check (after.registers.bank == (SramModel.snapshot ordinary.registers).bank)
        s!"ordinary controller boundary at edge {edge}"
      for p in ([0,1] : List (Fin 2)) do
        check (BitVec.ofNat 64 after.q[p.val]! == (ordinary.arrays p).q)
          s!"ordinary macro Q at edge {edge}"
        for k in [:64] do
          check (after.contents p (BitVec.ofNat 6 k) ==
            (ordinary.arrays p).contents (BitVec.ofNat 6 k))
            s!"ordinary SRAM contents at edge {edge}"
      ordinaryBoundaries := ordinaryBoundaries+1
    if after.core .valid == 1 then
      let count := (after.core .count).toNat
      for k in [:count] do
        let row := expected.values (.row (BitVec.ofNat 6 k))
        for p in ([0,1] : List (Fin 2)) do
          check (after.contents p (BitVec.ofNat 6 k) == row.extractLsb' 0 64)
            s!"resident physical replica {p} row {k} at edge {edge}"
          residentChecks := residentChecks+1
        check ((after.registers.values (.metadata (BitVec.ofNat 6 k))).toNat == row.toNat / 2^64)
          s!"resident metadata row {k} at edge {edge}"
        residentChecks := residentChecks+1
      for k in [:16] do
        check (after.registers.values (.branch (BitVec.ofNat 4 k)) ==
          expected.values (.branch (BitVec.ofNat 4 k))) s!"resident descriptor {k} at edge {edge}"
        residentChecks := residentChecks+1
      check (after.registers.values .startWord == (expected.values (.row 0)).extractLsb' 0 64)
        s!"resident START mirror at edge {edge}"
      residentChecks := residentChecks+1
      if storageMutations == 0 then
        let expectedWord := (expected.values (.row 0)).extractLsb' 0 64
        let changed := after.arrays[0]!.set! 0 ((after.arrays[0]![0]!) ^^^ 1)
        let mutant := {after with arrays := after.arrays.set! 0 changed}
        check (mutant.contents 0 0 != expectedWord) "physical instruction mutation must differ"
        let changedReference := expected.bank.set! 0 (expected.bank[0]! ^^^ 1)
        let mutantReference : Reference := ⟨changedReference⟩
        check (after.contents 0 0 != (mutantReference.values (.row 0)).extractLsb' 0 64)
          "independent reference instruction mutation must differ"
        storageMutations := 2
    let addr0 := ((SramCandidates.candidate false).eval (fun _ => 0) after.core).toNat % 64
    let addr1 := ((SramCandidates.candidate true).eval (fun _ => 0) after.core).toNat % 64
    let count := (after.core .count).toNat
    let ready (port address : Nat) := address >= count ||
      BitVec.ofNat 64 after.q[port]! == (expected.values (.row (BitVec.ofNat 6 address))).extractLsb' 0 64
    if after.core .valid == 1 then
      check (ready 0 addr0 && ready 1 addr1) s!"prospective SRAM response readiness at edge {edge}"
    result := result.push (Lean.Json.mkObj [("state",Lean.Json.mkObj state),
      ("fetch",Lean.Json.mkObj [("addr0",Lean.toJson addr0),("addr1",Lean.toJson addr1),
        ("q0",Lean.toJson after.q[0]!),("q1",Lean.toJson after.q[1]!),
        ("live0",Lean.toJson (decide (addr0 < count))),("live1",Lean.toJson (decide (addr1 < count))),
        ("ready",Lean.toJson (after.core .valid == 1 && ready 0 addr0 && ready 1 addr1)),
        ("startMirror",Lean.toJson (after.registers.values .startWord).toNat)])])
    actual := after
    reference := expected
  let report := Lean.Json.mkObj [("frames",Lean.toJson result),
    ("checks",Lean.Json.mkObj [("edges",Lean.toJson vectors.size),
      ("coreFieldChecks",Lean.toJson coreChecks),("publicOutputChecks",Lean.toJson outputChecks),
      ("residentFieldChecks",Lean.toJson residentChecks),
      ("ordinaryBoundaries",Lean.toJson ordinaryBoundaries),
      ("storageMutationControls",Lean.toJson storageMutations)])]
  IO.FS.writeFile (System.FilePath.mk (args[1]?.getD "")) (report.pretty ++ "\n")
  IO.println s!"Buffered explorer replay: {vectors.size} edges, {coreChecks} core checks, {outputChecks} outputs, {ordinaryBoundaries} ordinary boundaries."
'''


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pack(bits):
    return sum(int(bit) << index for index, bit in enumerate(bits))


def source_ref(path, start, end, label):
    return dict(path=path, start=start, end=end, label=label)


class RecordedEngine(BufferedEngine):
    def __init__(self, *args, **kwargs):
        self.raw_inputs = []
        super().__init__(*args, **kwargs)

    def step(self, raw_inputs):
        self.raw_inputs.append(raw_inputs)
        super().step(raw_inputs)


def source_state(engine):
    descriptor = engine.slot.descriptor
    bits = (engine.slot.peek(engine.identity).rx_bits if engine.done
            else tuple(engine.slot._rx))
    return dict(busy=int(not engine.done), levels=engine.levels, enabled=engine.enabled,
        virtual_pc=engine.pc, remaining=engine.remaining,
        tx_consumed=engine.slot._tx_consumed, rx_length=len(bits), rx_data=pack(bits),
        stage1=engine._first, stage2=engine._second,
        scratch=pack(engine.samples), phase=5 if engine.done else 1)


def wire_record(program, tx, rx, half):
    slot = TransferSlot(tx_capacity_bits=32, rx_capacity_bits=32)
    identity = slot.begin(program.key, program.encode_tx(tx), program.rx_reservation_bits)
    engine = RecordedEngine(slot, identity, program)
    peer = BufferedSPIPeer(tx, rx, half, 1)
    wire = BufferedWireSimulation(engine, peer)
    states = [source_state(engine)]
    observations = [wire.observation]
    while not engine.done:
        require(wire.cycle < 1000, 'Bounded SPI source execution exceeded its horizon')
        wire.step()
        states.append(source_state(engine))
        observations.append(wire.observation)
    completion = slot.peek(identity)
    require(completion.outcome == 'complete', 'SPI source transfer did not complete')
    require(program.decode_rx(completion.rx_bits) == rx, 'SPI source capture decode differs')
    peer_report = peer.check(completion.rx_bits)
    return engine.raw_inputs, states, observations, peer_report


def canonical_image(program):
    lowered = lower_sram(program)
    image = BufferedSramHardwareImage.from_bytes(lowered.to_bytes())
    require(image.to_bytes() == lowered.to_bytes(), 'Canonical SRAM image roundtrip changed bytes')
    controls = []
    for field in ('words', 'controls', 'branch_indices', 'branch_table'):
        arguments = dict(words=image.words, controls=image.controls,
            branch_indices=image.branch_indices, branch_table=image.branch_table)
        values = list(arguments[field])
        values[0] ^= 1
        arguments[field] = tuple(values)
        try:
            BufferedSramHardwareImage(**arguments, program_key=image.program_key, source=program)
        except ValueError:
            controls.append(dict(field=field, rejected=True))
        else:
            raise RuntimeError('Changed canonical SRAM ' + field + ' was admitted')
    return image, controls


def image_record(image, identifier, expression, label):
    return dict(id=identifier, label=label, target=image.image_format,
        programKey=image.program_key, imageKey=image.key,
        source=dict(expression=expression, definition=json.loads(image.to_bytes())['source']),
        virtualSpan=image.virtual_span, txBits=image.tx_bits, rxBits=image.rx_bits,
        wireOrder=image.wire_order, idleLevels=image.idle_levels, idleEnabled=image.idle_enabled,
        rows=[dict(pc=k, wordHex=f'0x{word:016x}', controlHex=f'0x{image.controls[k]:06x}',
            branchIndex=image.branch_indices[k], instruction=asdict(decode_reactive_instruction(word)),
            loop=asdict(decode_control(image.controls[k]))) for k, word in enumerate(image.words)],
        dictionary=[dict(index=k, wordHex=f'0x{word:014x}') for k, word in enumerate(image.branch_table)],
        storage=dict(image.storage(), instructionWordBits=64, metadataBits=28,
            physicalRowBits=92, dictionaryWordBits=56, instructionReplicas=2,
            allocatedInstructionSRAMBits=8192))


def build_transcript():
    programs = [compact_spi(4, 4), compact_spi(1, 6)]
    compiled = [canonical_image(program) for program in programs]
    images = [image_record(compiled[0][0], 'spi-four-byte', 'compact_spi(4, 4)', 'Four-byte mode-0 SPI'),
              image_record(compiled[1][0], 'spi-one-byte', 'compact_spi(1, 6)', 'One-byte mode-0 SPI, slower clock')]
    frames, expected, stages, transfers = [], {}, [], []

    def stage(identifier, title, description, refs=()):
        stages.append(dict(id=identifier, title=title, description=description,
            firstFrame=len(frames), lastFrame=None, sources=list(refs)))

    def edge(command=None, raw=3, event='', annotation='', image='spi-four-byte', transfer=None,
             want=None, source=None, wire=None):
        frame = dict(edge=len(frames), stage=stages[-1]['id'], event=event,
            annotation=annotation, command=command or {}, rawInputs=raw,
            imageId=image, transferLabel=transfer)
        if source is not None:
            frame['sourceState'] = source
        if wire is not None:
            frame['wire'] = dict(levels=wire.levels, enabled=wire.enabled, wires=wire.wires, known=wire.known)
        frames.append(frame)
        if want:
            expected[frame['edge']] = want
        stages[-1]['lastFrame'] = frame['edge']
        return frame['edge']

    stage('initialize', 'Initialize', 'A physical initialization edge establishes a new owner/coverage epoch. SRAM arrays and Q begin separately poisoned; initialization does not clear those arrays.')
    edge(dict(initialize=1), event='Initialize', annotation='Clear control ownership and upload knowledge while retaining unrelated physical array contents.',
         want=dict(valid=0,busy=0,retained=0,pending=0,generation=0,transfer=0))

    def upload(image, identifier, replacement=False):
        stage('replace' if replacement else 'load', 'Replace program' if replacement else 'Upload image',
            'Upload all sixteen dictionary entries and all four rows in the current epoch. Each accepted row broadcasts the instruction word to both SRAM replicas.')
        edge(event='Begin replacement' if replacement else 'Begin upload', image=identifier)
        for address, descriptor in enumerate(image.branch_table):
            if not replacement and address == 15:
                continue
            edge(dict(command=6,address=address,branch=descriptor),
                event=f'Dictionary {address}', annotation='Upload the complete 56-bit branch descriptor; unused slots are explicitly zero.',
                image=identifier, want=dict(valid=0,pending=1,rejected=0,busy=0,retained=0))
        for address, word in enumerate(image.words):
            edge(dict(command=1,address=address,word=word,control=image.controls[address],branch=image.branch_indices[address]),
                event=f'Row {address}', annotation='Broadcast-write the 64-bit instruction; latch its 24-bit loop metadata and 4-bit dictionary index.',
                image=identifier, want=dict(pending=1,rejected=0,busy=0,retained=0))
        commit = dict(command=2,count=len(image.words),virtual_span=image.virtual_span,
            idle_levels=image.idle_levels,idle_enabled=image.idle_enabled)
        if not replacement:
            edge(commit, event='Incomplete COMMIT rejected',
                annotation='Rows are present but descriptor 15 has not been uploaded in this epoch. COMMIT cannot establish VALID.',
                image=identifier, want=dict(valid=0,pending=1,rejected=1,generation=0))
            edge(dict(command=6,address=15,branch=image.branch_table[15]), event='Dictionary 15',
                annotation='Complete dictionary coverage before retrying COMMIT.', image=identifier,
                want=dict(valid=0,pending=1,rejected=0))
        stage('commit-replacement' if replacement else 'commit', 'Commit replacement' if replacement else 'Commit resident program',
            'COMMIT admits complete live coverage, installs count/virtual span/idle pins and advances generation. It establishes both replicas, metadata, dictionary and the row-zero START mirror.')
        edge(commit, event='COMMIT accepted', image=identifier,
            want=dict(valid=1,pending=0,busy=0,retained=0,rejected=0,generation=2 if replacement else 1))

    upload(compiled[0][0], 'spi-four-byte')

    configurations = [
        ('transfer-1','spi-four-byte',0,b'\x96\xa5\x3c\xc3',b'\xa6\x9b\x42\xe1',4,1,1),
        ('transfer-2','spi-four-byte',0,b'\x12\x34\x56\x78',b'\xde\xad\xbe\xef',4,1,2),
        ('transfer-3','spi-one-byte',1,b'\xa5',b'\x3c',6,2,3)]
    for identifier, image_id, image_number, tx, rx, half, generation, transfer in configurations:
        if image_number:
            upload(compiled[image_number][0],image_id,True)
        image, program = compiled[image_number][0], programs[image_number]
        raw_inputs, source_states, wire, peer = wire_record(program,tx,rx,half)
        stage('run' if transfer == 1 else 'reuse' if transfer == 2 else 'run-replacement',
            'Execute SPI' if transfer == 1 else 'Reuse resident program' if transfer == 2 else 'Execute replacement',
            'START copies the supplied TX wire bits and owns the reserved RX slot. The first row enters immediately through the START mirror. ' +
            ('No program upload occurs between transfers 1 and 2; only TX data and the peer reply change.' if transfer == 2 else 'The independent peer sees resolved pins and edge counts; it cannot inspect the program or engine.'))
        # Prior quiet controller edges consumed raw=3; both sampler registers are 3 at START.
        start = edge(dict(command=3,tx_data=pack(image.encode_tx(tx)),tx_length=image.tx_bits,
                rx_capacity=image.rx_reservation_bits,expected_generation=generation),
            event='START accepted', annotation='Enter SHIFT once: assert CS and consume the first TX bit. No SRAM fetch bubble precedes execution.',
            image=image_id,transfer=identifier,source=source_states[0],wire=wire[0],
            want=dict(valid=1,busy=1,retained=0,rejected=0,generation=generation,transfer=transfer))
        for cycle, raw in enumerate(raw_inputs,1):
            command, event, annotation, want = {}, '', '', None
            if cycle == 1 and transfer == 1:
                command=dict(command=1,address=0,word=3)
                event='Active write rejected'
                annotation='The owned running transfer rejects a row write and continues executing the resident program.'
                want=dict(rejected=1,busy=1,valid=1)
            elif source_states[cycle]['rx_length'] > source_states[cycle-1]['rx_length']:
                event=f'Capture RX bit {source_states[cycle]["rx_length"]-1}'
                annotation='KEEP entry appends the pre-edge second sampler bit to the owned RX prefix.'
            elif not source_states[cycle]['busy']:
                event='Engine complete'
                annotation='HALT restores the image idle pins and retains the completed RX result under its generation/transfer owner.'
            elif source_states[cycle]['virtual_pc'] != source_states[cycle-1]['virtual_pc']:
                event='Next instruction'
                annotation='Counted loop metadata selects the next physical row and virtual program position.'
            end = edge(command,raw,event,annotation,image_id,identifier,want,source_states[cycle],wire[cycle])
        transfers.append(dict(id=identifier,imageId=image_id,txHex=tx.hex(),expectedRxHex=rx.hex(),
            decodedRxHex=rx.hex(),startFrame=start,completeFrame=end,peer=peer))
        stage('retain' if transfer == 1 else f'retain-{transfer}', 'Read retained result',
            'Repeated STATUS and indexed reads preserve the completed RX prefix. Retained ownership blocks mutation until the matching RELEASE.')
        fingerprint=dict(busy=0,retained=1,phase=5,generation=generation,transfer=transfer,
            rx_length=image.rx_bits,rx_data=pack(program.encode_tx(rx)),tx_consumed=image.tx_bits)
        for index in (0,1,image.rx_bits-1):
            edge(dict(read_index=index),event=f'Read RX[{index}]',
                annotation='Read one retained wire-order bit without consuming the result.',image=image_id,transfer=identifier,
                want=dict(fingerprint,read_valid=1,read_bit=int(program.encode_tx(rx)[index])))
        edge(event='Stable retained STATUS',annotation='A quiet edge leaves the retained outcome, RX data and identity unchanged.',
            image=image_id,transfer=identifier,want=fingerprint)
        if transfer == 1:
            edge(dict(command=1,address=0,word=3),event='Retained write rejected',
                annotation='A completed result still owns the slot; replacing its program row is rejected.',
                image=image_id,transfer=identifier,want=dict(fingerprint,rejected=1))
            edge(dict(command=4,expected_generation=generation,expected_transfer=transfer+1),
                event='Stale RELEASE rejected',annotation='A mismatched transfer identity cannot release the retained result.',
                image=image_id,transfer=identifier,want=dict(fingerprint,rejected=1))
        stage('release' if transfer == 1 else f'release-{transfer}', 'Release owner',
            'A matching generation and transfer RELEASE frees the result slot while keeping the admitted resident program VALID.')
        edge(dict(command=4,expected_generation=generation,expected_transfer=transfer),event='RELEASE accepted',
            image=image_id,transfer=identifier,
            want=dict(valid=1,busy=0,retained=0,pending=0,rejected=0,generation=generation,transfer=transfer,rx_length=0,rx_data=0))
        edge(event='Resident program remains valid',image=image_id,
            want=dict(valid=1,busy=0,retained=0,generation=generation,transfer=transfer))

    for st in stages:
        require(st['lastFrame'] is not None, 'Empty recorded stage')
    sources = [
        source_ref('scripts/buffered_counted_hardware.py',303,316,'Data-independent counted SPI source'),
        source_ref('scripts/buffered_sram_hardware.py',1,68,'Strict canonical SRAM target image admission'),
        source_ref('scripts/buffered_shared_branches.py',163,200,'Dictionary, row and COMMIT host command contract'),
        source_ref('scripts/buffered_engine.py',375,409,'Source execution and two-stage sampler'),
        source_ref('scripts/buffered_peers.py',23,115,'Independent resolved-wire mode-0 SPI peer'),
        source_ref('Pinwheel/Hardware/Buffered/SramModel.lean',1,78,'Typed closed-loop SRAM/controller replay'),
        source_ref('Pinwheel/Hardware/Buffered/SramCorrespondence.lean',136,173,'Initialized binary resident-execution and observation theorems'),
        source_ref('docs/protocols/buffered-sram-loading.md',1,36,'Exact binary theorem boundary'),
        source_ref('docs/protocols/buffered-sram-loading.md',155,175,'Remaining source, serial and physical obligations'),
        source_ref('scripts/ExplorerBufferedSession.py',1,25,'Fresh bounded source/peer/typed session exporter')]
    stages = [dict(id='source',title='Write program',description='Describe a data-independent mode-0 SPI schedule. Two counted loops reuse SHIFT and KEEP rows across four bytes; payload is supplied later at START.',firstFrame=None,lastFrame=None,sources=sources[:1]),
        dict(id='lower',title='Lower to resident image',description='Strict canonical admission binds source identity to four instruction words, loop controls, dictionary indices and sixteen descriptors. The executable roundtrip rejects each changed field.',firstFrame=None,lastFrame=None,sources=sources[1:3])] + stages
    initialize_ref=source_ref('Pinwheel/Hardware/Buffered/SramCorrespondence.lean',95,134,'Initialization derives resident coverage and candidate-response readiness')
    execution_ref=source_ref('scripts/buffered_engine.py',494,544,'Source one-edge execution, countdown, sampler and dispatch')
    ownership_ref=source_ref('scripts/buffered_hardware.py',429,462,'Owned result fingerprint, stable indexed reads and matching RELEASE')
    retention_ref=source_ref('Pinwheel/Hardware/Buffered/ReactiveProofs.lean',87,114,'Kernel retained-result preservation')
    sources.extend([initialize_ref,execution_ref,ownership_ref,retention_ref])
    for st in stages[2:]:
        if st['id']=='initialize':
            st['sources']=[initialize_ref,sources[5]]
        elif st['id'] in ('load','replace'):
            st['sources']=[sources[2],sources[5]]
        elif st['id'].startswith('commit'):
            st['sources']=[initialize_ref,sources[6]]
        elif st['id'] in ('run','reuse','run-replacement'):
            st['sources']=[execution_ref,sources[4],sources[5],sources[6]]
        elif st['id'].startswith(('retain','release')):
            st['sources']=[ownership_ref,retention_ref,sources[6]]
        else:
            raise RuntimeError('Recorded stage has no source navigation: '+st['id'])
    return dict(schema='pinwheel-explorer-buffered-session-v1',id='buffered-spi-session',title='One engine, three programmable transfers',target=FORMAT,
        origin='Fresh source/peer transcript replayed by the actual typed Lean SRAM/controller model',
        scope='Finite executable witness at the SRAM core-command boundary. Python source execution supplies resolved digital peer inputs; fresh Lean SramModel replay supplies every displayed hardware state and is compared to an independently evolved SharedBranches full-register reference. Serial packet delivery, universal compiler/native/RTL refinement, electrical SRAM/CDC timing and physical-chip qualification are outside this recording.',
        convention='Each frame records post-edge controller outputs, except rejected: rejected is the command admission observation from the PRE-edge state. rawInputs is the resolved two-bit input consumed by sampler stage 1 on that edge; RX append reads the pre-edge stage-2 sample. remaining is the raw duration-minus-one counter. The SPI peer observes each resulting pin interval, with one-edge callback delay, two-edge sampler delay and tCO=1.',
        sourceRevision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        sources=sources,stages=stages,images=images,frames=frames,transfers=transfers,
        checks=dict(canonicalImageMutations=[dict(imageId=images[k]['id'],**control)
            for k,(_,controls) in enumerate(compiled) for control in controls],
            expectedCommandChecks=len(expected),sourceWireTransfers=len(transfers),
            sourceStateChecks=0,sourceWireChecks=0),
        obligations=[
            dict(id='binary',title='Initialized resident binary execution',status='Kernel theorem',
                description='Existing initialized_to_execution establishes the accepted resident-image runtime boundary for this target.',sources=[sources[6],sources[7]]),
            dict(id='source',title='SPI source to canonical resident image',status='Finite witness',
                description='This recording checks two canonical SPI programs against source execution and an independent peer. The execution-link panel shows the source/decoded-image theorem; its relation to packed circuit state remains open.',sources=[sources[0],sources[1]]),
            dict(id='serial',title='Serial requests and owned receipts',status='Open composition',
                description='The recording begins with delivered core commands. The pin serial frontend and its retained packet receipts need their own source-to-core composition.',sources=[sources[8]]),
            dict(id='physical',title='RTL and physical qualification',status='Separate gates',
                description='Digital model replay does not establish SRAM electrical timing, serial CDC/sampling, RTL refinement, placement/routing or package power.',sources=[sources[8]])]), expected


def replay(session, expected):
    lake = shutil.which('lake') or str(Path.home()/'.elan/bin/lake')
    require(Path(lake).is_file(), 'Pinned Lean lake executable is required')
    with tempfile.TemporaryDirectory(prefix='pinwheel-buffered-explorer-') as directory:
        folder=Path(directory)
        worker, request, report = folder/'Worker.lean', folder/'input.json', folder/'replay.json'
        worker.write_text(LEAN_WORKER)
        request.write_text(json.dumps(dict(vectors=[dict(command=f['command'],raw_inputs=f['rawInputs'])
            for f in session['frames']]),indent=2)+'\n')
        result=subprocess.run([lake,'env','lean','--run',str(worker),str(request),str(report)],
            cwd=ROOT,text=True,capture_output=True,timeout=1200)
        require(result.returncode==0, 'Fresh typed SRAM replay failed:\n'+result.stdout+result.stderr)
        print(result.stdout.strip(),flush=True)
        output=json.loads(report.read_text())
    require(len(output['frames'])==len(session['frames']), 'Typed replay changed frame count')
    for frame, recorded in zip(session['frames'],output['frames'],strict=True):
        state=recorded['state']
        frame['state']=state
        fetch=recorded['fetch']
        frame['fetch']=dict(addr0=fetch['addr0'],addr1=fetch['addr1'],
            q0Hex=f'0x{fetch["q0"]:016x}',q1Hex=f'0x{fetch["q1"]:016x}',
            startMirrorHex=f'0x{fetch["startMirror"]:016x}',
            live0=fetch['live0'],live1=fetch['live1'],ready=fetch['ready'])
        for key,value in expected.get(frame['edge'],{}).items():
            require(state[key]==value,f'Command contract {key} at edge {frame["edge"]}: {state[key]} != {value}')
        if 'sourceState' in frame:
            for key,value in frame['sourceState'].items():
                # The source engine ceases stepping its sampler after HALT;
                # actual hardware keeps sampling on terminal idle edges.
                if key in ('stage1','stage2') and not state['busy']:
                    continue
                require(state[key]==value,f'Source/typed {key} at edge {frame["edge"]}: {state[key]} != {value}')
                session['checks']['sourceStateChecks']+=1
            require(state['levels']<<2==frame['wire']['levels'] and state['enabled']<<2==frame['wire']['enabled'],
                f'Peer/typed pin drivers differ at edge {frame["edge"]}')
            session['checks']['sourceWireChecks']+=2
    for transfer in session['transfers']:
        end=session['frames'][transfer['completeFrame']]['state']
        image=next(i for i in session['images'] if i['id']==transfer['imageId'])
        bits=tuple(bool((end['rx_data']>>index)&1) for index in range(end['rx_length']))
        program=compact_spi(image['txBits']//8,transfer['peer']['half_cycles'])
        transfer['decodedRxHex']=program.decode_rx(bits).hex()
        require(transfer['decodedRxHex']==transfer['expectedRxHex'], 'Typed retained result differs from independent peer')
    session['checks'].update(output['checks'])
    session['checks']['passed']=True


def source_files(extra_roots=()):
    # Actual local import closure avoids unrelated work invalidating a trace.
    # The Lean toolchain/lake files bind external runtime/library resolution.
    files = {ROOT/name for name in ('lean-toolchain','lakefile.toml','lake-manifest.json')}
    pending = [Path(__file__), ROOT/'Pinwheel/Hardware/Buffered/SramModel.lean',
               ROOT/'Pinwheel/Hardware/Buffered/SramState.lean', *extra_roots]
    while pending:
        path=pending.pop()
        if path in files:
            continue
        files.add(path)
        if path.suffix=='.py':
            for node in ast.walk(ast.parse(path.read_text())):
                modules=([node.module] if isinstance(node,ast.ImportFrom)
                    else [item.name for item in node.names] if isinstance(node,ast.Import) else [])
                for module in modules:
                    if module:
                        local=ROOT/'scripts'/(module.replace('.','/')+'.py')
                        if local.is_file():
                            pending.append(local)
        else:
            for line in re.findall(r'^import\s+(.+)$',path.read_text(),re.MULTILINE):
                for module in line.split():
                    local=ROOT/(module.replace('.','/')+'.lean')
                    if local.is_file():
                        pending.append(local)
    return sorted(files)


def check_typed_constructor(session):
    """Bind the two finite source images to the new typed SPI constructor.

    The constructor's source/fetch/encoding/resident expansion theorems have
    their own kernel boundary. Matching its executable JSON is finite evidence
    about the Python canonical lowerer, rather than a universal Python proof.
    """
    lake = shutil.which('lake') or str(Path.home()/'.elan/bin/lake')
    source=ROOT/'test/BufferedSpiSource.lean'
    files=source_files((source,))
    before={str(path.relative_to(ROOT)):sha(path) for path in files}
    cases=[]
    for image in session['images']:
        byte_count=image['txBits']//8
        half_cycles=image['rows'][0]['instruction']['duration']
        command=[lake,'env','lean','--run',str(source),str(byte_count),str(half_cycles)]
        result=subprocess.run(command,cwd=ROOT,text=True,capture_output=True,timeout=120)
        require(result.returncode==0,'Typed SPI constructor export failed:\n'+result.stdout+result.stderr)
        exported=json.loads(result.stdout)
        require(exported['schema']=='pinwheel-buffered-spi-source-v1','Wrong typed constructor schema')
        expected=dict(words=[int(row['wordHex'],16) for row in image['rows']],
            controls=[int(row['controlHex'],16) for row in image['rows']],
            branch_indices=[row['branchIndex'] for row in image['rows']],
            branch_table=[int(row['wordHex'],16) for row in image['dictionary']],
            virtual_span=image['virtualSpan'],idle_levels=image['idleLevels'],
            idle_enabled=image['idleEnabled'],tx_bits=image['txBits'],rx_reservation_bits=image['rxBits'])
        require(all(exported[key]==value for key,value in expected.items()),
            'Typed SPI constructor differs from canonical Python SRAM image '+image['id'])
        cases.append(dict(imageId=image['id'],byteCount=byte_count,halfCycles=half_cycles,
            fieldsChecked=len(expected),passed=True))
    after={str(path.relative_to(ROOT)):sha(path) for path in files}
    require(before==after,'A typed constructor dependency changed during comparison; rerun after sources settle')
    for name,digest in session['sourceHashes'].items():
        require(after[name]==digest,'An execution dependency changed before constructor comparison: '+name)
    session['sourceHashes'].update(after)
    session['checks']['typedConstructorCases']=cases
    refs=[source_ref('Pinwheel/Program/BufferedSPI.lean',1,69,'Typed four-leaf counted SPI source and virtual fetch shape'),
          source_ref('Pinwheel/Hardware/Buffered/SpiSource.lean',1,110,'Supported linear encoding/decoding and resident expansion'),
          source_ref('test/BufferedSpiSource.lean',1,37,'Fresh typed constructor export compared to both canonical images'),
          source_ref('Pinwheel/Hardware/Buffered/SpiSource.lean',350,385,'Accepted canonical source-history and fixed-image runtime observation bridge')]
    session['sources'].extend(refs)
    session['stages'][0]['sources'].append(refs[0])
    session['stages'][1]['sources'].extend(refs[1:])
    session['stages'][1]['description']+=' Both image byte fields are also checked against the typed Lean SPI constructor; its source geometry, fetch shape, supported-leaf encoding and resident expansion have explicit kernel theorems.'
    session['obligations'].insert(1,dict(id='spi-constructor',title='Typed SPI source/image bridge',status='Bounded kernel bridge',
        description='For one fixed SPI configuration, cold initialization followed by SourceHistory-conforming accepted operands and a VALID cut derives the four-row count and exactly the source-constructed full-register binary image. Every permitted fixed-image runtime prefix then has matching public observations. Runtime excludes uploads, COMMIT and reset, including rejected writes. The mixed replacement and rejected-write paths in this recording remain finite executable evidence. The executable constructor matches both Python canonical images; the interpreter-to-packed-circuit relation and general compiler correctness remain open.',sources=refs))
    print('Typed SPI constructor: two images, eighteen exact field comparisons passed.',flush=True)


def transcript_digest(frames):
    return hashlib.sha256(json.dumps([dict(command=f['command'],raw_inputs=f['rawInputs'])
        for f in frames],sort_keys=True,separators=(',',':')).encode()).hexdigest()


def output_digest(frames):
    return hashlib.sha256(json.dumps([dict(state=f['state'],fetch=f['fetch']) for f in frames],
        sort_keys=True,separators=(',',':')).encode()).hexdigest()


def execution_evidence(frames, hashes):
    producer=Path(__file__).read_text()
    return dict(producerSHA256=hashlib.sha256(producer.encode()).hexdigest(),producerSource=producer,
        leanWorkerSHA256=hashlib.sha256(LEAN_WORKER.encode()).hexdigest(),
        transcriptSHA256=transcript_digest(frames),recordedOutputSHA256=output_digest(frames),
        sourceSHA256=hashes)


def check_source_operands(session):
    """Check finite accepted-operand witnesses, separately for each image epoch.

    rejected is the fresh typed PRE-edge admission result. Accepted row/table
    writes and COMMIT operands are compared to that epoch's canonical image.
    This does not assert one fixed-config SourceHistory for mixed replacement.
    """
    images={image['id']:image for image in session['images']}
    checked=0
    for frame in session['frames']:
        command=frame['command']
        op=command.get('command',0)
        if frame['state']['rejected'] or op not in (1,2,6):
            continue
        image=images[frame['imageId']]
        if op==1:
            row=image['rows'][command.get('address',0)]
            require(command.get('word',0)==int(row['wordHex'],16) and
                command.get('control',0)==int(row['controlHex'],16) and
                command.get('branch',0)==row['branchIndex'], 'Accepted row operand differs from source image')
        elif op==6:
            require(command.get('branch',0)==int(image['dictionary'][command.get('address',0)]['wordHex'],16),
                'Accepted descriptor differs from source image')
        else:
            require(command['count']==4 and command['virtual_span']==image['virtualSpan'] and
                command['idle_levels']==4 and command['idle_enabled']==7,
                'Accepted COMMIT operands differ from source geometry')
        checked+=1
    require(checked==42,'Expected 32 accepted dictionary, 8 row and 2 COMMIT source-operand witnesses')
    session['checks']['acceptedSourceOperandChecks']=checked


def refresh_metadata():
    """Refresh prose/source navigation while retaining verified execution bytes.

    Require the retained producer, identical embedded Lean worker and identical
    command/input transcript, identical current source-generated frame skeleton,
    images and transfers, and unchanged execution dependencies. The original
    producer source and hashes remain in executionEvidence. Constructor exports
    and their proof dependency hashes are checked afresh. Runtime changes require
    the normal full generation path.
    """
    recorded=json.loads(OUTPUT.read_text())
    evidence=recorded['executionEvidence']
    require(hashlib.sha256(evidence['producerSource'].encode()).hexdigest()==evidence['producerSHA256'],
        'Retained execution producer source is corrupt')
    require(hashlib.sha256(LEAN_WORKER.encode()).hexdigest()==evidence['leanWorkerSHA256'],
        'Lean execution worker changed; use full generation')
    require(transcript_digest(recorded['frames'])==evidence['transcriptSHA256'],
        'Retained command/input transcript changed')
    require(output_digest(recorded['frames'])==evidence['recordedOutputSHA256'],
        'Retained execution outputs changed; use full generation')
    files=source_files()
    before={str(path.relative_to(ROOT)):sha(path) for path in files}
    own=str(Path(__file__).relative_to(ROOT))
    require(set(before)==set(evidence['sourceSHA256']), 'Execution dependency closure changed; use full generation')
    for name,digest in before.items():
        if name!=own:
            require(digest==evidence['sourceSHA256'][name],'Execution dependency changed; use full generation: '+name)
    fresh,expected=build_transcript()
    require(fresh['images']==recorded['images'] and fresh['transfers']==recorded['transfers'],
        'Source program/images/transfer witnesses changed; use full generation')
    require(len(fresh['frames'])==len(recorded['frames']),'Recording length changed; use full generation')
    for generated,actual in zip(fresh['frames'],recorded['frames'],strict=True):
        require(generated=={key:value for key,value in actual.items() if key not in ('state','fetch')},
            'Source-generated frame changed; use full generation')
        for key,value in expected.get(actual['edge'],{}).items():
            require(actual['state'][key]==value,'Retained state no longer meets its command witness')
    require(transcript_digest(fresh['frames'])==evidence['transcriptSHA256'],'New command/input transcript differs')
    fresh['frames']=recorded['frames']
    fresh['checks']=recorded['checks']
    fresh['executionEvidence']=evidence
    fresh['executionEvidence']['metadataRefreshedWithoutExecutionChange']=True
    fresh['sourceHashes']=before
    check_typed_constructor(fresh)
    check_source_operands(fresh)
    require(all(sha(ROOT/name)==digest for name,digest in fresh['sourceHashes'].items()),
        'A dependency changed during metadata refresh')
    OUTPUT.write_text(json.dumps(fresh,indent=2,sort_keys=True)+'\n')
    print('Refreshed metadata and constructor source pins; all 691 verified execution states unchanged.',flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--refresh-metadata',action='store_true',help='Refresh only prose/navigation after exact retained-execution checks')
    args=parser.parse_args()
    if args.refresh_metadata:
        refresh_metadata()
        return
    files=source_files()
    before={str(path.relative_to(ROOT)):sha(path) for path in files}
    session,expected=build_transcript()
    replay(session,expected)
    after={str(path.relative_to(ROOT)):sha(path) for path in files}
    require(before==after,'A recording dependency changed during generation; rerun after changes settle')
    session['sourceHashes']=before
    session['executionEvidence']=execution_evidence(session['frames'],before)
    check_typed_constructor(session)
    check_source_operands(session)
    OUTPUT.write_text(json.dumps(session,indent=2,sort_keys=True)+'\n')
    print(f'Built {OUTPUT.relative_to(ROOT)} ({len(session["frames"])} edges; {len(session["transfers"])} source/peer/typed transfers).',flush=True)


if __name__=='__main__':
    main()
