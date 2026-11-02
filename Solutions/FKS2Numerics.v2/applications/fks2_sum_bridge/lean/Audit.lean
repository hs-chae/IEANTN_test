import FKS2SumBridge
import Lean.Util.CollectAxioms

#print axioms FKS2SumBridge.complete_sum_bridge
#print axioms FKS2SumBridge.complete_full_connection
#print axioms FKS2SumBridge.scoped_RN64
#print axioms FKS2SumBridge.traceLoop_project
#print axioms FKS2SumBridge.source_trace_execution
#print axioms FKS2SumBridge.concrete_source_executions
#print axioms FKS2SumBridge.rounding_bounds
#print axioms FKS2SumBridge.first_term_error
#print axioms FKS2SumBridge.second_term_error
#print axioms FKS2SumBridge.terms_to_IEANTN
#print axioms FKS2SumBridge.IEANTN_sum_errors
#print axioms FKS2SumBridge.coefficient_error
#print axioms FKS2SumBridge.new_whole_forward_error
#print axioms FKS2SumBridge.new_relaxed_upper_bound
set_option pp.explicit true in
#print FKS2SumBridge.complete_sum_bridge
set_option pp.explicit true in
#print FKS2SumBridge.complete_full_connection
set_option pp.explicit true in
#print FKS2SumBridge.SourceIdentity
set_option pp.explicit true in
#print FKS2SumBridge.TraceConnection
set_option pp.explicit true in
#print SumStability.RN64
set_option pp.explicit true in
#print SumStability.Binary64
#print SumStability.ValidInputs
#print SumStability.RepresentsInput
#print SumStability.ExecC
#print SumStability.CState

#print axioms FKS2SumBridge.eta_nonneg
#print axioms FKS2SumBridge.sum_abs_term_bounds
#print axioms FKS2SumBridge.specification_sum_errors
#print axioms FKS2SumBridge.rational_specification_errors
#print axioms FKS2SumBridge.first_loop_forward_error
#print axioms FKS2SumBridge.second_loop_forward_error
#print axioms FKS2SumBridge.whole_error_via_specification
#print axioms FKS2SumBridge.selected_fks2_error_via_stability
#print axioms FKS2SumBridge.concrete_fks2_error_via_stability
#print axioms FKS2SumBridge.relaxed_upper_bound_via_stability
#print axioms FKS2SumBridge.integration_budget_checks
#print axioms FKS2SumBridge.complete_integration
set_option pp.explicit true in
#print FKS2SumBridge.eta_nonneg
set_option pp.explicit true in
#print FKS2SumBridge.sum_abs_term_bounds
set_option pp.explicit true in
#print FKS2SumBridge.specification_sum_errors
set_option pp.explicit true in
#print FKS2SumBridge.rational_specification_errors
set_option pp.explicit true in
#print FKS2SumBridge.first_loop_forward_error
set_option pp.explicit true in
#print FKS2SumBridge.second_loop_forward_error
set_option pp.explicit true in
#print FKS2SumBridge.whole_error_via_specification
set_option pp.explicit true in
#print FKS2SumBridge.selected_fks2_error_via_stability
set_option pp.explicit true in
#print FKS2SumBridge.concrete_fks2_error_via_stability
set_option pp.explicit true in
#print FKS2SumBridge.relaxed_upper_bound_via_stability
set_option pp.explicit true in
#print FKS2SumBridge.integration_budget_checks
set_option pp.explicit true in
#print FKS2SumBridge.complete_integration

#print FKS2SumBridge.Iteration
#print FKS2SumBridge.LoopTrace
#print FKS2Scalar.ExecC
#print SumStability.c_sum_forward_error_real

#print axioms FKS2SumBridge.corrected_node_multiplier
#print FKS2SumBridge.corrected_node_multiplier

open Lean in
run_elab do
  let env ← getEnv
  let roots := #[`FKS2SumBridge.complete_sum_bridge, `FKS2SumBridge.complete_full_connection, `FKS2SumBridge.scoped_RN64, `FKS2SumBridge.traceLoop_project, `FKS2SumBridge.source_trace_execution, `FKS2SumBridge.concrete_source_executions, `FKS2SumBridge.rounding_bounds, `FKS2SumBridge.first_term_error, `FKS2SumBridge.second_term_error, `FKS2SumBridge.terms_to_IEANTN, `FKS2SumBridge.IEANTN_sum_errors, `FKS2SumBridge.coefficient_error, `FKS2SumBridge.new_whole_forward_error, `FKS2SumBridge.new_relaxed_upper_bound, `FKS2SumBridge.eta_nonneg, `FKS2SumBridge.sum_abs_term_bounds, `FKS2SumBridge.specification_sum_errors, `FKS2SumBridge.rational_specification_errors, `FKS2SumBridge.first_loop_forward_error, `FKS2SumBridge.second_loop_forward_error, `FKS2SumBridge.whole_error_via_specification, `FKS2SumBridge.selected_fks2_error_via_stability, `FKS2SumBridge.concrete_fks2_error_via_stability, `FKS2SumBridge.relaxed_upper_bound_via_stability, `FKS2SumBridge.integration_budget_checks, `FKS2SumBridge.complete_integration, `FKS2SumBridge.corrected_node_multiplier]
  let allowed := [`FKS2SumBridge.integration_budget_checks._native.native_decide.ax_1_1, `propext, `Classical.choice, `Quot.sound, `FKS2Scalar.fixed_execution._native.native_decide.ax_1_1, `FKS2Scalar.source_checked._native.native_decide.ax_1_1, `FKS2Scalar.sum1_checks._native.native_decide.ax_1_1, `FKS2Scalar.sum2_checks._native.native_decide.ax_1_1, `FKS2Scalar.target_enclosure._native.native_decide.ax_1_1, `FKS2Scalar.z_exp_checks._native.native_decide.ax_1_1, `FKS2SumBridge.composition_checks._native.native_decide.ax_1_1, `FKS2SumBridge.concrete_trace_checks._native.native_decide.ax_1_1, `FKS2SumBridge.extracted_sum_indexing._native.native_decide.ax_1_1, `FKS2SumBridge.source_trace_execution._native.native_decide.ax_1_1]
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
      let ty ← if name.toString.startsWith "FKS2SumBridge." || name.toString.startsWith "SumStability." || name.toString.startsWith "FKS2Scalar." then
        pure (toString (← Lean.Meta.ppExpr ci.type)) else pure ""
      declarations := declarations.push (Json.mkObj [
        ("name", toJson name.toString), ("kind", toJson kind), ("type", toJson ty),
        ("dependencies", toJson (deps.map Name.toString))])
    let forbidden := [`FKS2Scalar.forward_error, `FKS2Scalar.budget_forward_error,
      `FKS2Scalar.roundoff_certificate, `FKS2Scalar.rational_certificate,
      `FKS2Scalar.complete_result, `FKS2Scalar.connected_result, `FKS2Scalar.selected_source_error]
    for name in forbidden do
      if seen.contains name then throwError "forbidden old whole-error dependency in {root}: {name}"
    let newConsumed := [`FKS2SumBridge.specification_sum_errors,
      `FKS2SumBridge.rational_specification_errors, `FKS2SumBridge.first_loop_forward_error,
      `FKS2SumBridge.second_loop_forward_error, `FKS2SumBridge.whole_error_via_specification,
      `FKS2SumBridge.selected_fks2_error_via_stability,
      `FKS2SumBridge.concrete_fks2_error_via_stability,
      `FKS2SumBridge.relaxed_upper_bound_via_stability, `FKS2SumBridge.complete_integration, `FKS2SumBridge.corrected_node_multiplier]
    if newConsumed.contains root then
      for name in [`FKS2SumBridge.new_whole_forward_error, `FKS2SumBridge.IEANTN_sum_errors,
        `FKS2SumBridge.hybrid_sum_error, `FKS2SumBridge.complete_full_connection] do
        if seen.contains name then throwError "old bridge accuracy bypass in {root}: {name}"
      unless seen.contains `FKS2SumBridge.specification_sum_errors do
        throwError "missing specification error dependency in {root}"
    if root == `FKS2SumBridge.complete_sum_bridge ||
        root == `FKS2SumBridge.complete_full_connection || newConsumed.contains root then
      unless seen.contains `SumStability.c_sum_forward_error_real do
        throwError "missing genuine general C stability dependency in {root}"
    results := results.push (Json.mkObj [
      ("root", toJson root.toString), ("count", toJson declarations.size),
      ("type", toJson (toString (← Lean.Meta.ppExpr rootCI.type))),
      ("axioms", toJson (axioms.toList.map Name.toString)),
      ("declarations", Json.arr declarations)])
  IO.FS.writeFile "../evidence/dependency_closure.json" (Json.arr results).compress
