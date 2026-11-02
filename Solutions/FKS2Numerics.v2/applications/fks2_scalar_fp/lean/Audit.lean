import FKS2Scalar
import Lean.Util.CollectAxioms

#print axioms FKS2Scalar.complete_result
#print axioms FKS2Scalar.original_threshold_discrepancy
#print axioms FKS2Scalar.target_normalization

open Lean in
run_elab do
  let env ← getEnv
  let roots := #[`FKS2Scalar.complete_result, `FKS2Scalar.original_threshold_discrepancy]
  let mut results : Array Json := #[]
  for root in roots do
    let mut pending := [root]
    let mut seen : NameSet := {}
    let mut declarations : Array Json := #[]
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if seen.contains name then continue
      seen := seen.insert name
      let some ci := env.find? name | throwError "missing dependency {name}"
      let deps := ci.getUsedConstantsAsSet.toList
      pending := deps ++ pending
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .defnInfo _ => "definition"
        | _ => "kernel-declaration"
      let ty ← if name.toString.startsWith "FKS2Scalar." then
        pure (toString (← Lean.Meta.ppExpr ci.type)) else pure ""
      declarations := declarations.push (Json.mkObj [
        ("name", toJson name.toString), ("kind", toJson kind), ("type", toJson ty),
        ("dependencies", toJson (deps.map Name.toString))])
    let axioms ← Lean.collectAxioms root
    results := results.push (Json.mkObj [
      ("root", toJson root.toString), ("count", toJson declarations.size),
      ("axioms", toJson (axioms.toList.map Name.toString)),
      ("declarations", Json.arr declarations)])
  IO.FS.writeFile "../evidence/dependency_closure.json" (Json.arr results).compress

#eval FKS2Scalar.outputBits
#eval FKS2Scalar.q
#eval FKS2Scalar.E
#eval FKS2Scalar.Bpoc - (FKS2Scalar.q + FKS2Scalar.E)
#eval FKS2Scalar.helperEvents.length
