import SynergyHeightC.SourcePNTFromSemanticOutputs
import Lean
open Lean Meta Elab
set_option maxHeartbeats 0
run_elab do
 let env ← getEnv
 let families := ["SynergyAnalytic.ContinuousProfile","SynergyAnalytic.ProfileRegularity",
  "SynergyAnalytic.ClosedCount","SynergyAnalytic.HeightEnvelope","SynergyAnalytic.CoarseCount",
  "SynergyAnalytic.CoarseProfile","SynergyAnalytic.CoarseTwoThousand",
  "SynergyAnalytic.SourceReciprocal","SynergyAnalytic.EndpointCells"]
 let names := env.checked.get.constants.fold (fun acc n ci =>
  match env.getModuleIdxFor? n with
  | none => acc
  | some idx =>
   match env.header.moduleNames[idx.toNat]? with
   | none => acc
   | some owner => if families.contains owner.toString then acc.push (n,ci) else acc)
  (#[] : Array (Name × ConstantInfo))
 for (n,ci) in names do
  let proof ← isProp ci.type
  let value ← if proof then pure "PROOF_BODY_EXCLUDED_TYPES_CHECKED" else
   match ci with
   | .defnInfo d => pure (reprStr d.value)
   | .opaqueInfo d => pure (reprStr d.value)
   | _ => throwError "unhandled nonproof declaration {n}"
  logInfo m!"IDENTITY_ROW {(Json.mkObj [("name",toJson n.toString),("proof",toJson proof),("type",toJson (reprStr ci.type)),("data",toJson value)]).compress}"
