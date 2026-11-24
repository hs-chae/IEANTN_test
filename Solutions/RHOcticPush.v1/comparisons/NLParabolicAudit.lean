import NLParabolicConsumer
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned := #[`NLParabolicComparison,`NLParabolicConsumer]
  let mut count : Nat := 0
  for (name,index) in env.const2ModIdx.toList do
    let module := (env.header.moduleNames[index.toNat]?).getD .anonymous
    if !owned.contains module then continue
    let some (.thmInfo _) := env.find? name | continue
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext,`Classical.choice,`Quot.sound].contains) do
      throwError "Nonstandard NL comparison axiom {name}: {axioms}"
    logInfo m!"NL_PARABOLIC_THEOREM {(Json.mkObj [("name",toJson name.toString),("module",toJson module.toString),("axioms",toJson (axioms.map Name.toString))]).compress}"
    count := count+1
  unless count == 27 do throwError "Expected all27 actual compiler-owned theorem roots: {count}"
  logInfo m!"NL_PARABOLIC_AUDIT_PASS {count}"
  let root := `RHOcticPush.NLParabolicComparison.actual_prime_count_beats_old_objective
  let some info := env.find? root | throwError "Missing actual prime-count consumer"
  let some value := info.value? true | throwError "Missing actual consumer proof VALUE"
  let used := value.getUsedConstants
  let required := #[`RHOcticPush.OptimizedFinal.strict_count_214891875,
    `RHOcticPush.NLParabolicComparison.new_count_factor_larger,
    `RHOcticPush.NLParabolicComparison.new_interval_shorter]
  for target in required do
    unless used.contains target do throwError "Actual consumer does not use {target}"
  logInfo m!"NL_PARABOLIC_VALUE_PATH {(Json.mkObj [("root",toJson root.toString),("required",toJson (required.map Name.toString)),("checked_value_edges",toJson required.size)]).compress}"
