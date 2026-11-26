/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveBodyAST
import FFTWordSlices
import FFTWordArithmetic
import FFTWordDivision
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

theorem add_expr_eval {F : Type} (context : Context F) {state : State F}
    {a b : Expr} {x y : Nat}
    (left : Eval context state a (.integer (integer64 x)) state)
    (right : Eval context state b (.integer (integer64 y)) state)
    (hx : x < 2^64) (hy : y < 2^64) (sum : x+y < 2^64) :
    Eval context state (addExpr a b) (.integer (integer64 (x+y))) state := by
  apply Eval.paren
  refine .binaryLR left right ?_
  simpa only [binary,Option.map_some] using
    congrArg (Option.map Value.integer) (binary64_add x y hx hy sum)

theorem mul_expr_eval {F : Type} (context : Context F) {state : State F}
    {a b : Expr} {x y : Nat}
    (left : Eval context state a (.integer (integer64 x)) state)
    (right : Eval context state b (.integer (integer64 y)) state)
    (hx : x < 2^64) (hy : y < 2^64) (product : x*y < 2^64) :
    Eval context state (mulExpr a b) (.integer (integer64 (x*y))) state := by
  apply Eval.paren
  refine .binaryLR left right ?_
  simpa only [binary,Option.map_some] using
    congrArg (Option.map Value.integer) (binary64_mul x y hx hy product)

theorem div_expr_eval {F : Type} (context : Context F) {state : State F}
    {a b : Expr} {x y : Nat}
    (left : Eval context state a (.integer (integer64 x)) state)
    (right : Eval context state b (.integer (integer64 y)) state)
    (hx : x < 2^64) (hy : y < 2^64) (positive : 0 < y) :
    Eval context state (.paren (.binary .div a b)) (.integer (integer64 (x/y))) state := by
  apply Eval.paren
  refine .binaryLR left right ?_
  simpa only [binary,Option.map_some] using
    congrArg (Option.map Value.integer) (binary64_div x y hx hy positive)

/-- Actual source pointer addition with the full word-index and multiplication
checks, for an arbitrary pure index expression into the caller's real array. -/
theorem cell_pointer_eval {F : Type} (context : Context F) {state : State F}
    {pointer index : Expr} {object size k : Nat} {data : Nat → Nat}
    (sourcePointer : Eval context state pointer (.pointer (wordPointer object 0)) state)
    (sourceIndex : Eval context state index (.integer (integer64 k)) state)
    (array : WordArrayRep state object size data)
    (indexFit : k < 2^64) (productFit : k*12 < 2^64) (bound : k*12 < size) :
    Eval context state (addExpr pointer (mulExpr index (literal 12)))
      (.pointer (wordPointer object (k*12))) state := by
  have multiplied := mul_expr_eval context sourceIndex
    (Eval.literal (.integer 12 "ULL") _ (.integer (integer64 12)) (by rfl))
    indexFit (by norm_num) productFit
  apply Eval.paren
  refine .binaryLR sourcePointer multiplied ?_
  have added := slice_pointer_add (start:=0) (i:=k*12) array (by omega)
  simpa only [binary,Option.map_some,Nat.zero_add] using congrArg (Option.map Value.pointer) added

#print axioms cell_pointer_eval
end RH080Next.FFTPV.RecursiveSource
