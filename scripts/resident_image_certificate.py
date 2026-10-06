"""Untrusted renderer for the separately named resident source certificate.

Lean independently checks every source word, every successor/operand and the
actual upload transcript. This certificate does not assert physical SRAM or
complete timed package refinement.
"""
import re

from paired_image_certificate import _values


MARKER = 'Resident image certificate: kernel checked; standard axioms only.'


def render(name, source_words, last, idle, image, uploaded):
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', name):
        raise ValueError('Invalid certificate name')
    if not 1 <= len(source_words) <= 256 or type(last) is not int or not 0 <= last < len(source_words):
        raise ValueError('Resident source capacity/last address')
    _values(idle, 2, 3)
    source = _values([*source_words, *([4] * (256-len(source_words)))], 256, 64)
    parameters = _values(image.parameters, 32, 20)
    rows = _values(image.rows, 256, 64)
    boot = _values([image.boot], 1, 32)
    _values(image.idle, 2, 3)
    raw = _values(uploaded, len(uploaded), 64)
    return f'''import Pinwheel.Hardware.Storage.PairedResidentImage
import Lean

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Pinwheel.Artifact.ResidentImage.{name}
open Pinwheel.Hardware.Storage
open PairedResidentImage
def source : Source := {{
  words := #v[{source}]
  idle := ⟨{idle[0]}, {idle[1]}⟩
  last := ⟨{last}, by decide⟩ }}
def image : PairedImage.Image := {{
  parameters := #v[{parameters}]
  rows := #v[{rows}]
  boot := {boot}
  idle := {image.idle[0] | image.idle[1] << 3} }}
def uploaded : List (BitVec 64) := [{raw}]
theorem accepted : check source image uploaded = true := by
  decide +kernel
  done
end Pinwheel.Artifact.ResidentImage.{name}

open Lean Elab Command in
elab "#audit_resident_image_certificate" : command => do
  let env ← getEnv
  let expected := ``Pinwheel.Artifact.ResidentImage.{name}.accepted
  unless env.contains expected do throwError "Missing resident image certificate"
  for theoremName in [expected, ``Pinwheel.Hardware.Storage.PairedResidentImage.checked_trace] do
    let axioms ← collectAxioms theoremName
    let unexpected := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless unexpected.isEmpty do throwError "Unapproved resident image certificate axioms: {{unexpected}}"
  logInfo "{MARKER}"
#audit_resident_image_certificate
'''
