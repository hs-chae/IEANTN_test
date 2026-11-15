import ScopedIO.PrintSBuffer
import Lean.Util.CollectAxioms
open Lean Elab
set_option maxHeartbeats 0
run_elab do
 let env ← getEnv
 for n in ([`ScopedIO.PrintSBuffer.unwritten,`ScopedIO.PrintSBuffer.append_digit,`ScopedIO.PrintSBuffer.cast_digit,`ScopedIO.PrintSBuffer.store_prefix,`ScopedIO.PrintSBuffer.write_digit,`ScopedIO.PrintSBuffer.capacity_guard] : List Name) do
  let some ci := env.find? n | throwError "missing declaration {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"BUILD_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
