import Lean
import StreamingUARTRequiredTargets

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
          (#["ReadyCoreD2Audit", "ReadyCoreD2Endpoints", "ReadyCoreD2Graphs", "ReadyCoreD2Hints", "ReadyCoreD2Links", "ReadyCoreD2LocalProofs", "ReadyCoreD2Model", "ReadyCoreD2PrivateAxiom", "ReadyCoreD2Proof", "ReadyCoreD2RejectAxiom", "ReadyCoreD2Sources", "ReadyCoreD4Audit", "ReadyCoreD4Endpoints", "ReadyCoreD4Graphs", "ReadyCoreD4Hints", "ReadyCoreD4Links", "ReadyCoreD4LocalProofs", "ReadyCoreD4Model", "ReadyCoreD4PrivateAxiom", "ReadyCoreD4Proof", "ReadyCoreD4RejectAxiom", "ReadyCoreD4Sources", "ReadyQuadFrontendAudit", "ReadyQuadFrontendEndpoints", "ReadyQuadFrontendGraphs", "ReadyQuadFrontendHints", "ReadyQuadFrontendLinks", "ReadyQuadFrontendLocalProofs", "ReadyQuadFrontendModel", "ReadyQuadFrontendPrivateAxiom", "ReadyQuadFrontendProof", "ReadyQuadFrontendRejectAxiom", "ReadyQuadFrontendSources", "StreamingReadySessionD2", "StreamingReadySessionD4", "StreamingReadyWrappersD2", "StreamingReadyWrappersD4", "StreamingUARTRequiredTargets", "StreamingUARTSessionD2", "StreamingUARTSessionD4"] : Array String).contains owner
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
