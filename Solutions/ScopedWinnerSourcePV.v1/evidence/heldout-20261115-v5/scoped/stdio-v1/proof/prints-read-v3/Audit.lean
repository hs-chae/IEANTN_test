import ScopedIO.PrintSRead
import Lean.Util.CollectAxioms
open Lean Elab
set_option maxHeartbeats 0
run_elab do
 let env ← getEnv
 for n in ([`ScopedIO.PrintSRead.buffer_object,`ScopedIO.PrintSRead.written_cell,`ScopedIO.PrintSRead.array_value,`ScopedIO.PrintSRead.index_value,`ScopedIO.PrintSRead.digit_argument,`ScopedIO.PrintSRead.source_putchar] : List Name) do
  let some ci := env.find? n | throwError "missing declaration {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"BUILD_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
