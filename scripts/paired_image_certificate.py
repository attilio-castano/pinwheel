"""Render untrusted paired-image data for the Lean kernel's certificate checker.

The source is canonical E64 bytes, independently decoded by Lean. The candidate
is the actual parameter/row/boot/idle image plus its actual upload words. This
renderer does not assert correctness; the generated theorem must typecheck.
"""
import re


def _values(values, count, width):
    values = list(values)
    if len(values) != count or any(type(v) is not int or not 0 <= v < 1 << width for v in values):
        raise ValueError(f'Expected {count} unsigned {width}-bit values')
    return ', '.join(str(v) for v in values)


def render(name, source_words, last, idle, image, uploaded):
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', name):
        raise ValueError('Invalid certificate name')
    if not 1 <= len(source_words) <= 256 or type(last) is not int or not 0 <= last < 256:
        raise ValueError('Source capacity/last address')
    _values(idle, 2, 3)
    source = _values([*source_words, *([4] * (256-len(source_words)))], 256, 64)
    parameters = _values(image.parameters, 32, 20)
    rows = _values(image.rows, 256, 64)
    boot = _values([image.boot], 1, 32)
    _values(image.idle, 2, 3)
    raw = _values(uploaded, len(uploaded), 64)
    return f'''import Pinwheel.Hardware.Storage.PairedImage
import Lean

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Pinwheel.Artifact.PairedImage.{name}
open Pinwheel.Hardware
open Pinwheel.Hardware.Storage.PairedImage
def sourceWords : Execution.Words := #v[{source}]
def source : Execution.Image := {{
  memory := sourceWords.map (fun w => (Execution.decode w).getD .halt)
  idle := ⟨{idle[0]}, {idle[1]}⟩
  last := ⟨{last}, by decide⟩ }}
def image : Image := {{
  parameters := #v[{parameters}]
  rows := #v[{rows}]
  boot := {boot}
  idle := {image.idle[0] | image.idle[1] << 3} }}
def uploaded : List (BitVec 64) := [{raw}]
theorem accepted : Execution.imageWords source = sourceWords ∧
    check source image uploaded = true := by
  decide +kernel
  done
end Pinwheel.Artifact.PairedImage.{name}

open Lean Elab Command in
elab "#audit_paired_image_certificate" : command => do
  let env ← getEnv
  let expected := ``Pinwheel.Artifact.PairedImage.{name}.accepted
  unless env.contains expected do throwError "Missing image certificate"
  for theoremName in [expected, ``Pinwheel.Hardware.Storage.PairedImage.checked_trace] do
    let axioms ← collectAxioms theoremName
    let unexpected := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless unexpected.isEmpty do throwError "Unapproved image certificate axioms: {{unexpected}}"
  logInfo "Paired image certificate: kernel checked; standard axioms only."
#audit_paired_image_certificate
'''
