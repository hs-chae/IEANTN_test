import ScopedIO.PrintSEntry
import Lean.Util.CollectAxioms
open Lean Elab
set_option maxHeartbeats 0
run_elab do
 let env ← getEnv
 for n in ([`ScopedIO.PrintSEntry.arguments,`ScopedIO.PrintSEntry.count_declaration,`ScopedIO.PrintSEntry.a_at,`ScopedIO.PrintSEntry.negative_expression,`ScopedIO.PrintSEntry.magnitude_expression,`ScopedIO.PrintSEntry.x_declaration,`ScopedIO.PrintSEntry.first_declaration,`ScopedIO.PrintSEntry.pop_body,`ScopedIO.PrintSEntry.pop_call] : List Name) do
  let some ci := env.find? n | throwError "missing declaration {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"BUILD_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
