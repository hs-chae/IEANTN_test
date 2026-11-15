import ScopedIO.PrintSFrames
import Lean.Util.CollectAxioms
open Lean Elab
set_option maxHeartbeats 0
run_elab do
 let env ← getEnv
 for n in ([`ScopedIO.PrintSFrames.cells_length,`ScopedIO.PrintSFrames.actual_uninitialized_array,`ScopedIO.PrintSFrames.count_at,`ScopedIO.PrintSFrames.decrement_source,`ScopedIO.PrintSFrames.positive_source] : List Name) do
  let some ci := env.find? n | throwError "missing declaration {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"BUILD_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
