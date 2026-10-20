import Lean
import StreamingRequiredTargets

open Lean Elab Command

/-- Audit the compiled environment, including private declarations and definitions
whose fields contain proofs. Source-text theorem discovery is insufficient here. -/
elab "#audit_pinwheel" : command => do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx =>
        let owner := env.header.modules[idx.toNat]!.module.toString
        owner == "Pinwheel" || owner.startsWith "Pinwheel." ||
          (#["CoreD2Audit", "CoreD2Endpoints", "CoreD2Graphs", "CoreD2Hints", "CoreD2Links", "CoreD2LocalProofs", "CoreD2Model", "CoreD2PrivateAxiom", "CoreD2Proof", "CoreD2RejectAxiom", "CoreD2Sources", "CoreD4Audit", "CoreD4Endpoints", "CoreD4Graphs", "CoreD4Hints", "CoreD4Links", "CoreD4LocalProofs", "CoreD4Model", "CoreD4PrivateAxiom", "CoreD4Proof", "CoreD4RejectAxiom", "CoreD4Sources", "QuadFrontendAudit", "QuadFrontendEndpoints", "QuadFrontendGraphs", "QuadFrontendHints", "QuadFrontendLinks", "QuadFrontendLocalProofs", "QuadFrontendModel", "QuadFrontendPrivateAxiom", "QuadFrontendProof", "QuadFrontendRejectAxiom", "QuadFrontendSources", "StreamingRequiredTargets", "StreamingSessionD2", "StreamingSessionD4", "StreamingWrappersD2", "StreamingWrappersD4"] : Array String).contains owner
      | none => info.isAxiom || info.isTheorem
    if owned then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved axioms in {name}: {unexpected}"
  if declarations == 0 || theorems == 0 then
    throwError "Empty Pinwheel proof audit"
  logInfo m!"Pinwheel audit: {declarations} declarations, {theorems} theorems; standard axioms only."

#audit_pinwheel
