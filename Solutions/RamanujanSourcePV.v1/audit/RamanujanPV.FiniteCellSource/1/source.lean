/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.FiniteLogSource
import RamanujanPV.FiniteExpSource
namespace RamanujanPV.FiniteCellSource
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def cellFunction : Function := ⟨"int","rpc_finite_cell",[("uint64_t","n"),("uint64_t","next"),("uint64_t","j"),("uint64_t","P"),("uint64_t","Q"),("uint64_t","Lu"),("uint64_t","A")],(.sequence [(.branch (.binary "<" (.var "n") (.nat 38358837683)) (.returnStmt (.nat 0)) .skip),(.branch (.binary "<=" (.var "next") (.var "n")) (.returnStmt (.nat 0)) .skip),(.branch (.binary ">" (.var "next") (.nat 2000000000001)) (.returnStmt (.nat 0)) .skip),(.branch (.binary ">" (.var "j") (.var "n")) (.returnStmt (.nat 0)) .skip),(.branch (.binary ">" (.var "Q") (.var "j")) (.returnStmt (.nat 0)) .skip),(.branch (.binary ">" (.var "P") (.binary "-" (.var "next") (.nat 1))) (.returnStmt (.nat 0)) .skip),(.branch (.binary "==" (.var "Lu") (.nat 0)) (.returnStmt (.nat 0)) .skip),(.branch (.binary "!=" (.var "Lu") (.call (.var "rpc_log_upper") [(.var "n")])) (.returnStmt (.nat 0)) .skip),(.declare [⟨"uint64_t","lo",some (.call (.var "rpc_e_low") [])⟩]),(.declare [⟨"uint64_t","hi",some (.call (.var "rpc_e_high") [])⟩]),(.branch (.binary ">" (.binary "*" (.cast "__uint128_t" (.var "j")) (.var "hi")) (.binary "*" (.cast "__uint128_t" (.var "n")) (.nat 1152921504606846976))) (.returnStmt (.nat 0)) .skip),(.branch (.binary "!=" (.cast "__uint128_t" (.var "A")) (.binary "/" (.binary "*" (.cast "__uint128_t" (.var "n")) (.var "lo")) (.var "Lu"))) (.returnStmt (.nat 0)) .skip),(.returnStmt (.binary "<" (.binary "*" (.binary "*" (.cast "__uint128_t" (.nat 1048576)) (.var "P")) (.var "P")) (.binary "*" (.cast "__uint128_t" (.var "A")) (.var "Q"))))])⟩
def render (_ : Unit) : Option String := do
  return "/*\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n*/\n#include <stdint.h>\n#include \"verified_finite_exp.c\"\n#include \"verified_finite_log.c\"\n\n"++(←renderFunctions [cellFunction])
def actualSource : String := include_str "../c/verified_finite_cell.c"
theorem actual_source_bytes : render ()=some actualSource := by decide +kernel
theorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource () :=
  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource () actual_source_bytes (by decide +kernel)
#print axioms actual_source_bytes
#print axioms actual_source_checked
end RamanujanPV.FiniteCellSource
