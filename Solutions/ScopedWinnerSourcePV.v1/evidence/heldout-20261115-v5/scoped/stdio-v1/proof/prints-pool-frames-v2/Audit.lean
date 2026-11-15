import ScopedIO.PrintSPoolFrames
import Lean.Util.CollectAxioms
open Lean Elab
set_option maxHeartbeats 0
run_elab do
 let env ← getEnv
 for n in ([`ScopedIO.PrintSPoolFrames.parameter_context,`ScopedIO.PrintSPoolFrames.buffer_context,`ScopedIO.PrintSPoolFrames.frame_context,`ScopedIO.PrintSPoolFrames.buffer_binary,`ScopedIO.PrintSPoolFrames.frame_binary,`ScopedIO.PrintSPoolFrames.next_framed,`ScopedIO.PrintSPoolFrames.advance_framed] : List Name) do
  let some ci := env.find? n | throwError "missing declaration {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"BUILD_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
