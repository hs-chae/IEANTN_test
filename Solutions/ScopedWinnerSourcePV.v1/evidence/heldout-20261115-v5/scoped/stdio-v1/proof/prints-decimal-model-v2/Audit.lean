import ScopedIO.PrintSDecimalModel
import Lean.Util.CollectAxioms
open Lean Elab
set_option maxHeartbeats 0
run_elab do
 let env ← getEnv
 for n in ([`ScopedIO.PrintSDecimalModel.digits_step,`ScopedIO.PrintSDecimalModel.digits_ne_nil,`ScopedIO.PrintSDecimalModel.digit_lt,`ScopedIO.PrintSDecimalModel.ofDigits_digits,`ScopedIO.PrintSDecimalModel.quotient_step,`ScopedIO.PrintSDecimalModel.remainder_digit,`ScopedIO.PrintSDecimalModel.digits_capacity,`ScopedIO.PrintSDecimalModel.source_guard,`ScopedIO.PrintSDecimalModel.bytes_valid,`ScopedIO.PrintSDecimalModel.signedBytes_valid,`ScopedIO.PrintSDecimalModel.output_represents] : List Name) do
  let some ci := env.find? n | throwError "missing declaration {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"BUILD_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
