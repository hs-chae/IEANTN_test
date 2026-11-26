/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveSource
import FapFFTRecursiveSource
import FFTProductRowPrefix
set_option autoImplicit false
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect

def loopBody : Stmt:=
  (.block [(.declare .u64 "e" (some (.call "encoded_node" [(.variable "j")]))), (.declare .u64 "value" (some (.literal (.integer 0 "ULL")))), (.declare .u64 "sign" (some (.literal (.integer 0 "ULL")))), (.ite (.binary .ge (.variable "e") (.literal (.integer 10000000000000000 "ULL"))) (.block [(.assign (.variable "value") (.paren (.binary .sub (.variable "e") (.literal (.integer 10000000000000000 "ULL")))))]) (some (.block [(.assign (.variable "value") (.paren (.binary .sub (.literal (.integer 10000000000000000 "ULL")) (.variable "e")))), (.assign (.variable "sign") (.literal (.integer 1 "ULL")))]))), (.declare .u64 "scaled" (some (.paren (.binary .mul (.variable "value") (.literal (.integer 100 "ULL")))))), (.declare (.pointer .u64) "p" (some (.paren (.binary .add (.variable "data") (.paren (.binary .mul (.variable "j") (.literal (.integer 12 "ULL")))))))), (.assign (.index (.variable "p") (.literal (.integer 2 "ULL"))) (.paren (.binary .mod (.variable "scaled") (.literal (.integer 1000000000 "ULL"))))), (.assign (.variable "scaled") (.paren (.binary .div (.variable "scaled") (.literal (.integer 1000000000 "ULL"))))), (.assign (.index (.variable "p") (.literal (.integer 3 "ULL"))) (.paren (.binary .mod (.variable "scaled") (.literal (.integer 1000000000 "ULL"))))), (.assign (.index (.variable "p") (.literal (.integer 4 "ULL"))) (.paren (.binary .div (.variable "scaled") (.literal (.integer 1000000000 "ULL"))))), (.assign (.index (.variable "p") (.literal (.integer 5 "ULL"))) (.variable "sign")), (.expression (.call "canonical_sign" [(.variable "p")])), (.ite (.binary .gt (.variable "j") (.literal (.integer 0 "ULL"))) (.block [(.expression (.call "copy_words" [(.paren (.binary .add (.variable "data") (.paren (.binary .mul (.paren (.binary .sub (.variable "n") (.variable "j"))) (.literal (.integer 12 "ULL")))))), (.variable "p"), (.literal (.integer 12 "ULL"))]))]) none), (.assign (.variable "j") (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL")))))])

def loop (count : Nat) : Stmt:=.whileLoop (.binary .lt (.variable "j") (.literal (.integer count "ULL"))) loopBody

theorem actual_w4_input_loop :
    (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[21]?=some (loop 2520):=by rfl

theorem actual_fap_input_loop :
    (ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body)[21]?=some (loop 400):=by rfl

#print axioms actual_w4_input_loop
#print axioms actual_fap_input_loop
end RH080Next.FFTPV.InputLoader
