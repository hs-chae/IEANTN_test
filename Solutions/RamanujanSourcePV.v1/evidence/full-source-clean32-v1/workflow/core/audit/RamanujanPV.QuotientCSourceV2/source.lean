/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LCMSourcePV.ASTLoops
namespace RamanujanPV.QuotientCSourceV2
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sqrtFunction : Function := ⟨"uint64_t","rpc_isqrt",[("uint64_t","n")],(.sequence [(.declare [⟨"uint64_t","r",some (.nat 0)⟩]),(.whileLoop (.binary "<=" (.binary "+" (.var "r") (.nat 1)) (.binary "/" (.var "n") (.binary "+" (.var "r") (.nat 1)))) (.sequence [(.eval (.unary "++" (.var "r")))])),(.returnStmt (.var "r"))])⟩
def countFunction : Function := ⟨"uint64_t","rpc_quotient_count",[("uint64_t","n"),("uint64_t","capacity"),("uint64_t*","small"),("uint64_t*","large")],(.sequence [(.branch (.binary "<" (.var "n") (.nat 2)) (.returnStmt (.nat 0)) .skip),(.branch (.binary ">" (.var "n") (.nat 2000000000000)) (.returnStmt (.nat 0)) .skip),(.declare [⟨"uint64_t","r",some (.call (.var "rpc_isqrt") [(.var "n")])⟩]),(.branch (.binary "<=" (.var "capacity") (.var "r")) (.returnStmt (.nat 0)) .skip),(.forLoop (.declare [⟨"uint64_t","i",some (.nat 1)⟩]) (some (.binary "<=" (.var "i") (.var "r"))) (.unary "++" (.var "i")) (.sequence [(.eval (.binary "=" (.index (.var "small") (.var "i")) (.binary "-" (.var "i") (.nat 1)))),(.eval (.binary "=" (.index (.var "large") (.var "i")) (.binary "-" (.binary "/" (.var "n") (.var "i")) (.nat 1))))])),(.forLoop (.declare [⟨"uint64_t","p",some (.nat 2)⟩]) (some (.binary "<=" (.var "p") (.var "r"))) (.unary "++" (.var "p")) (.branch (.binary "==" (.index (.var "small") (.var "p")) (.index (.var "small") (.binary "-" (.var "p") (.nat 1)))) .skip (.sequence [(.declare [⟨"uint64_t","before",some (.index (.var "small") (.binary "-" (.var "p") (.nat 1)))⟩]),(.declare [⟨"uint64_t","stop",some (.var "r")⟩]),(.branch (.binary "<" (.binary "/" (.var "n") (.binary "*" (.var "p") (.var "p"))) (.var "r")) (.eval (.binary "=" (.var "stop") (.binary "/" (.var "n") (.binary "*" (.var "p") (.var "p"))))) .skip),(.forLoop (.declare [⟨"uint64_t","i",some (.nat 1)⟩]) (some (.binary "<=" (.var "i") (.var "stop"))) (.unary "++" (.var "i")) (.sequence [(.declare [⟨"uint64_t","ip",some (.binary "*" (.var "i") (.var "p"))⟩]),(.declare [⟨"uint64_t","sub",some (.nat 0)⟩]),(.branch (.binary "<=" (.var "ip") (.var "r")) (.eval (.binary "=" (.var "sub") (.index (.var "large") (.var "ip")))) (.eval (.binary "=" (.var "sub") (.index (.var "small") (.binary "/" (.var "n") (.var "ip")))))),(.branch (.binary "<" (.var "sub") (.var "before")) (.returnStmt (.nat 0)) .skip),(.branch (.binary "<" (.index (.var "large") (.var "i")) (.binary "-" (.var "sub") (.var "before"))) (.returnStmt (.nat 0)) .skip),(.eval (.binary "=" (.index (.var "large") (.var "i")) (.binary "-" (.index (.var "large") (.var "i")) (.binary "-" (.var "sub") (.var "before")))))])),(.declare [⟨"uint64_t","square",some (.binary "*" (.var "p") (.var "p"))⟩]),(.branch (.binary "<=" (.var "square") (.var "r")) (.sequence [(.declare [⟨"uint64_t","v",some (.var "r")⟩]),(.whileLoop (.binary "<=" (.var "square") (.var "v")) (.sequence [(.declare [⟨"uint64_t","sub",some (.index (.var "small") (.binary "/" (.var "v") (.var "p")))⟩]),(.branch (.binary "<" (.var "sub") (.var "before")) (.returnStmt (.nat 0)) .skip),(.branch (.binary "<" (.index (.var "small") (.var "v")) (.binary "-" (.var "sub") (.var "before"))) (.returnStmt (.nat 0)) .skip),(.eval (.binary "=" (.index (.var "small") (.var "v")) (.binary "-" (.index (.var "small") (.var "v")) (.binary "-" (.var "sub") (.var "before"))))),(.eval (.unary "--" (.var "v")))]))]) .skip)]))),(.returnStmt (.index (.var "large") (.nat 1)))])⟩
def functions : List Function := [sqrtFunction,countFunction]
def render (_ : Unit) : Option String := do
  return "/*\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n*/\n#include <stdint.h>\n\n"++(←renderFunctions functions)
def actualSource : String := include_str "../c/verified_quotient_count.c"
/-- Exact complete source bytes, including its copyright comment. The
untrusted deterministic renderer proposal is checked by the Lean kernel. -/
theorem actual_source_bytes : render ()=some actualSource := by decide +kernel
/-- Byte identity avoids evaluating two full lexical scans. Only the actual
source's successful restricted scan remains a numerical kernel obligation. -/
theorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource () :=
  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource ()
    actual_source_bytes (by decide +kernel)
#print axioms actual_source_bytes
#print axioms actual_source_checked
end RamanujanPV.QuotientCSourceV2
