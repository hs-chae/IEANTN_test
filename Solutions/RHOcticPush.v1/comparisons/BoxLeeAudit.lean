import BoxVsLee
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, i) in env.const2ModIdx.toList do
    if (env.header.moduleNames[i.toNat]?).getD .anonymous != `BoxVsLee then continue
    let some ci := env.find? n | continue
    if !ci.isTheorem then continue
    let axs ← collectAxioms n
    unless axs.all (#[`propext, `Classical.choice, `Quot.sound].contains) do
      throwError "Nonstandard axiom: {n}: {axs}"
    logInfo m!"BOX_LEE_THEOREM {Json.compress (Json.mkObj [("name",toJson n.toString),("axioms",toJson (axs.map Name.toString))])}"
    count := count + 1
  unless count == 15 do throwError "Expected all fifteen actual theorem constants: {count}"
  logInfo m!"BOX_LEE_ALL15_PASS"
