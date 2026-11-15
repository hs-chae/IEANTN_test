import ScopedIO.PrintSDigitExpression
import Lean.Util.CollectAxioms
open Lean Elab
set_option maxHeartbeats 0
run_elab do
 let env ← getEnv
 for n in ([`ScopedIO.PrintSDigitExpression.digit_sum,`ScopedIO.PrintSDigitExpression.digit_conversion,`ScopedIO.PrintSDigitExpression.index_address,`ScopedIO.PrintSDigitExpression.store_expression] : List Name) do
  let some ci := env.find? n | throwError "missing declaration {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"BUILD_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
