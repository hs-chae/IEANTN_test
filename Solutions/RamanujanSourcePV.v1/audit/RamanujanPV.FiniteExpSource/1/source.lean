/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LCMSourcePV.ASTLoops
namespace RamanujanPV.FiniteExpSource
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lowFunction : Function := ⟨"uint64_t","rpc_e_low",[],(.sequence [(.declare [⟨"uint64_t","term",some (.nat 1152921504606846976)⟩]),(.declare [⟨"uint64_t","total",some (.nat 1152921504606846976)⟩]),(.forLoop (.declare [⟨"uint64_t","k",some (.nat 1)⟩]) (some (.binary "<=" (.var "k") (.nat 20))) (.unary "++" (.var "k")) (.sequence [(.eval (.binary "=" (.var "term") (.binary "/" (.var "term") (.var "k")))),(.eval (.binary "=" (.var "total") (.binary "+" (.var "total") (.var "term"))))])),(.returnStmt (.var "total"))])⟩
def highFunction : Function := ⟨"uint64_t","rpc_e_high",[],(.sequence [(.returnStmt (.binary "+" (.call (.var "rpc_e_low") []) (.nat 22)))])⟩
def functions : List Function := [lowFunction,highFunction]
def render (_ : Unit) : Option String := do
  return "/*\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n*/\n#include <stdint.h>\n\n"++(←renderFunctions functions)
def actualSource : String := include_str "../c/verified_finite_exp.c"
theorem actual_source_bytes : render ()=some actualSource := by decide +kernel
theorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource () :=
  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource () actual_source_bytes (by decide +kernel)
#print axioms actual_source_bytes
#print axioms actual_source_checked
end RamanujanPV.FiniteExpSource
