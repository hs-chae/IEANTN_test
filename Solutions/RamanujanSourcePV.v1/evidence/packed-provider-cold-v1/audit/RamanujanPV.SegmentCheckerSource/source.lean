/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCMachine
namespace RamanujanPV.SegmentCheckerSource
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def checkerFunction : Function := ⟨"uint64_t","rpc_check_segment",[("uint64_t","lo"),("uint64_t","hi"),("uint64_t","capacity"),("uint64_t*","claims"),("uint64_t*","flags")],(.sequence [(.branch (.binary "<" (.var "lo") (.nat 2)) (.returnStmt (.nat 0)) .skip),(.branch (.binary "<" (.var "hi") (.var "lo")) (.returnStmt (.nat 0)) .skip),(.branch (.binary ">" (.var "hi") (.nat 2000000000000)) (.returnStmt (.nat 0)) .skip),(.declare [⟨"uint64_t","length",some (.binary "+" (.binary "-" (.var "hi") (.var "lo")) (.nat 1))⟩]),(.branch (.binary "<" (.var "capacity") (.var "length")) (.returnStmt (.nat 0)) .skip),(.forLoop (.declare [⟨"uint64_t","i",some (.nat 0)⟩]) (some (.binary "<" (.var "i") (.var "length"))) (.unary "++" (.var "i")) (.eval (.binary "=" (.index (.var "flags") (.var "i")) (.nat 1)))),(.forLoop (.declare [⟨"uint64_t","d",some (.nat 2)⟩]) (some (.binary "<=" (.var "d") (.binary "/" (.var "hi") (.var "d")))) (.unary "++" (.var "d")) (.sequence [(.declare [⟨"uint64_t","first",some (.binary "*" (.binary "/" (.var "lo") (.var "d")) (.var "d"))⟩]),(.branch (.binary "<" (.var "first") (.var "lo")) (.eval (.binary "=" (.var "first") (.binary "+" (.var "first") (.var "d")))) .skip),(.branch (.binary "<" (.var "first") (.binary "*" (.var "d") (.var "d"))) (.eval (.binary "=" (.var "first") (.binary "*" (.var "d") (.var "d")))) .skip),(.forLoop (.declare [⟨"uint64_t","m",some (.var "first")⟩]) (some (.binary "<=" (.var "m") (.var "hi"))) (.binary "=" (.var "m") (.binary "+" (.var "m") (.var "d"))) (.eval (.binary "=" (.index (.var "flags") (.binary "-" (.var "m") (.var "lo"))) (.nat 0))))])),(.declare [⟨"uint64_t","count",some (.nat 0)⟩]),(.forLoop (.declare [⟨"uint64_t","i",some (.nat 0)⟩]) (some (.binary "<" (.var "i") (.var "length"))) (.unary "++" (.var "i")) (.sequence [(.branch (.binary "==" (.index (.var "claims") (.var "i")) (.index (.var "flags") (.var "i"))) .skip (.returnStmt (.nat 0))),(.eval (.binary "=" (.var "count") (.binary "+" (.var "count") (.index (.var "flags") (.var "i")))))])),(.returnStmt (.binary "+" (.var "count") (.nat 1)))])⟩
def functions : List Function := [checkerFunction]
def render (program : List Function) : Option String := do
  return "/*\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n*/\n#include <stdint.h>\n\n" ++ (←renderFunctions program)
def actualSource : String := include_str "../c/verified_segment_checker.c"
theorem actual_source_bytes : render functions = some actualSource := by decide +kernel
theorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource functions :=
  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource functions
    actual_source_bytes (by decide +kernel)
theorem source_expression_depth : QuotientCMachine.stmtWithin 4 32 checkerFunction.body = true := by decide +kernel
#print axioms actual_source_checked
#print axioms source_expression_depth
end RamanujanPV.SegmentCheckerSource
