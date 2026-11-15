import ScopedIO.WorldPureLift
import Lean.Util.CollectAxioms
open Lean Elab
set_option maxHeartbeats 0
run_elab do
 let env ← getEnv
 for n in ([`ScopedIO.WorldPureLift.eval,`ScopedIO.WorldPureLift.declare,`ScopedIO.WorldPureLift.scope,`ScopedIO.WorldPureLift.guard,`ScopedIO.WorldPureLift.statement,`ScopedIO.WorldPureLift.while_run] : List Name) do
  let some ci := env.find? n | throwError "missing declaration {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"BUILD_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
