import SumStability
import Lean.Util.CollectAxioms

#print axioms SumStability.source_and_forward_error
#print axioms SumStability.rn_relative
#print axioms SumStability.accum_invariant
#print axioms SumStability.next_operation_safe
#print axioms SumStability.c_sum_finite_normal
#print axioms SumStability.half_formal_execution
#print axioms SumStability.halves_formal_execution

set_option pp.explicit true in
#print SumStability.c_sum_forward_error_real
#print SumStability.ValidInputs
#print SumStability.Binary64
#print SumStability.EvenLSB
#print SumStability.RN64
#print SumStability.ExecC
#print SumStability.ForExec
#print SumStability.RepresentsInput
#print SumStability.selectedSumProgram
#print SumStability.CState

open Lean in
run_elab do
  let env ← getEnv
  let roots := #[`SumStability.source_and_forward_error,
    `SumStability.c_sum_forward_error_real, `SumStability.rn_relative, `SumStability.rn_delta,
    `SumStability.accum_invariant, `SumStability.next_operation_safe,
    `SumStability.c_sum_finite_normal, `SumStability.half_formal_execution,
    `SumStability.halves_formal_execution, `SumStability.selected_source_checked]
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut results : Array Json := #[]
  for root in roots do
    let some rootCI := env.find? root | throwError "missing root {root}"
    let axioms ← Lean.collectAxioms root
    for ax in axioms do
      unless allowed.contains ax do
        throwError "unapproved axiom in {root}: {ax}"
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
      let ty ← if name.toString.startsWith "SumStability." then
        pure (toString (← Lean.Meta.ppExpr ci.type)) else pure ""
      declarations := declarations.push (Json.mkObj [
        ("name", toJson name.toString), ("kind", toJson kind), ("type", toJson ty),
        ("dependencies", toJson (deps.map Name.toString))])
    results := results.push (Json.mkObj [
      ("root", toJson root.toString), ("count", toJson declarations.size),
      ("type", toJson (toString (← Lean.Meta.ppExpr rootCI.type))),
      ("axioms", toJson (axioms.toList.map Name.toString)),
      ("declarations", Json.arr declarations)])
  IO.FS.writeFile "../evidence/dependency_closure.json" (Json.arr results).compress
