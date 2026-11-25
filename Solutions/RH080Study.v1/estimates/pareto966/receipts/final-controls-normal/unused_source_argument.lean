import Lean
import ParetoSolution
open Lean Elab Command
theorem unused_source (h:Buthe.v1.theorem_2_theta) : True := True.intro
run_cmd do
 let env←getEnv
 let some (.thmInfo t):=env.find? `unused_source | throwError "Missing fixture"
 match t.value with
 | .lam _ _ b _ => unless b.hasLooseBVar 0 do throwError "REJECT_REQUIRED_SOURCE_INPUT_NOT_CONSUMED"
 | _ => throwError "Malformed fixture"
