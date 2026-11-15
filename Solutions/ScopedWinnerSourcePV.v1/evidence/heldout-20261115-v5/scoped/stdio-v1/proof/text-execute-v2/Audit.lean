import ScopedIO.TextExecute
import Lean.Util.CollectAxioms
open Lean Elab
set_option maxHeartbeats 0
run_elab do
 let env ← getEnv
 for n in ([`ScopedIO.TextExecute.declaration_sound,`ScopedIO.TextExecute.leave_scope,`ScopedIO.TextExecute.sound,`ScopedIO.TextExecute.statement_sound] : List Name) do
  let some ci := env.find? n | throwError "missing declaration {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"BUILD_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
