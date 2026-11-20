/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LCMSourcePV.ASTLoops
namespace RamanujanPV.FiniteLogSource
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
def ceilFunction : Function := ⟨"uint64_t","rpc_log_ceildiv",[("__uint128_t","a"),("__uint128_t","b")],(.sequence [(.branch (.binary "==" (.var "b") (.nat 0)) (.returnStmt (.cast "uint64_t" (.nat 0))) .skip),(.returnStmt (.cast "uint64_t" (.binary "+" (.binary "/" (.var "a") (.var "b")) (.binary "!=" (.binary "%" (.var "a") (.var "b")) (.nat 0)))))])⟩
def seriesFunction : Function := ⟨"uint64_t","rpc_log_series_upper",[("uint64_t","num"),("uint64_t","den")],(.sequence [(.declare [⟨"uint64_t","F",some (.nat 1152921504606846976)⟩]),(.declare [⟨"uint64_t","z",some (.call (.var "rpc_log_ceildiv") [(.binary "*" (.cast "__uint128_t" (.var "F")) (.var "num")),(.var "den")])⟩]),(.declare [⟨"uint64_t","z2",some (.call (.var "rpc_log_ceildiv") [(.binary "*" (.cast "__uint128_t" (.var "z")) (.var "z")),(.var "F")])⟩]),(.declare [⟨"uint64_t","power",some (.var "z")⟩]),(.declare [⟨"__uint128_t","sum",some (.nat 0)⟩]),(.forLoop (.declare [⟨"uint64_t","k",some (.nat 0)⟩]) (some (.binary "<" (.var "k") (.nat 20))) (.unary "++" (.var "k")) (.sequence [(.eval (.binary "=" (.var "sum") (.binary "+" (.var "sum") (.call (.var "rpc_log_ceildiv") [(.var "power"),(.binary "+" (.binary "*" (.nat 2) (.var "k")) (.nat 1))])))),(.eval (.binary "=" (.var "power") (.call (.var "rpc_log_ceildiv") [(.binary "*" (.cast "__uint128_t" (.var "power")) (.var "z2")),(.var "F")])))])),(.returnStmt (.cast "uint64_t" (.binary "+" (.binary "*" (.nat 2) (.var "sum")) (.call (.var "rpc_log_ceildiv") [(.binary "*" (.binary "*" (.cast "__uint128_t" (.nat 2)) (.var "power")) (.var "F")),(.binary "*" (.cast "__uint128_t" (.nat 41)) (.binary "-" (.var "F") (.var "z2")))]))))])⟩
def upperFunction : Function := ⟨"uint64_t","rpc_log_upper",[("uint64_t","n")],(.sequence [(.branch (.binary "<" (.var "n") (.nat 2)) (.returnStmt (.cast "uint64_t" (.nat 0))) .skip),(.declare [⟨"uint64_t","two",some (.nat 1)⟩]),(.declare [⟨"uint64_t","k",some (.nat 0)⟩]),(.whileLoop (.binary "<=" (.var "two") (.binary "/" (.var "n") (.nat 2))) (.sequence [(.eval (.binary "=" (.var "two") (.binary "*" (.var "two") (.nat 2)))),(.eval (.unary "++" (.var "k")))])),(.declare [⟨"uint64_t","log2",some (.call (.var "rpc_log_series_upper") [(.nat 1),(.nat 3)])⟩]),(.returnStmt (.call (.var "rpc_log_ceildiv") [(.binary "+" (.binary "*" (.cast "__uint128_t" (.var "k")) (.var "log2")) (.call (.var "rpc_log_series_upper") [(.binary "-" (.var "n") (.var "two")),(.binary "+" (.var "n") (.var "two"))])),(.nat 1048576)]))])⟩
def functions : List Function := [ceilFunction,seriesFunction,upperFunction]
def render (_ : Unit) : Option String := do
  return "/*\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n*/\n#include <stdint.h>\n\n"++(←renderFunctions functions)
def actualSource : String := include_str "../c/verified_finite_log.c"
theorem actual_source_bytes : render ()=some actualSource := by decide +kernel
theorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource () :=
  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource () actual_source_bytes (by decide +kernel)
#print axioms actual_source_bytes
#print axioms actual_source_checked
end RamanujanPV.FiniteLogSource
