/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveHeaderView
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
namespace Header

theorem View.parameter {F : Type} (context : Context F) {state : State F}
    {total : Nat} {buffers : Buffers total} {start index step n count owner : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : View state buffers start index step n count ids owner input table output work) (v : Var) :
    Eval context state (.variable (name v))
      (value (buffers.object .output) (buffers.object .input) (buffers.object .twiddle)
        (buffers.object .work) start index step n total v) state :=
  .variable (h.bindings.lookup (.inl v) trivial) (h.bindings.read (.inl v) trivial)

theorem View.half_expr {F : Type} (context : Context F) {state : State F}
    {total : Nat} {buffers : Buffers total} {start index step n count owner : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : View state buffers start index step n count ids owner input table output work)
    (hn : n<2^64) : Eval context state
      (.paren (.binary .div (.variable "n") (literal 2))) (.integer (integer64 (n/2))) state :=
  div_expr_eval context (h.parameter context .n)
    (.literal (.integer 2 "ULL") _ (.integer (integer64 2)) (by rfl)) hn (by norm_num) (by decide)

theorem View.arguments_eval {F : Type} (context : Context F) {state : State F}
    {total : Nat} {buffers : Buffers total} {start index step n half count owner : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : View state buffers start index step n count ids owner input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half) (positive : 0<half)
    (initialized : 0<count) (right : Bool) :
    Args context state (recursiveArguments right)
      (arguments (buffers.object .output) (buffers.object .input) (buffers.object .twiddle)
        (buffers.object .work) (if right then start+half else start)
        (if right then index+step else index) (step*2) half total) state := by
  have bounds := shape.scalar_bounds
  have children := shape.children split positive
  have lb := children.1.scalar_bounds
  have rb := children.2.scalar_bounds
  have halfEq : n/2=half := by omega
  have halfActive : Active count (.inr .half) := by exact initialized
  have halfE : Eval context state (.variable "half") (.integer (integer64 half)) state := by
    simpa [loopName,localName,loopValue,halfEq] using
      (Eval.variable (h.bindings.lookup (.inr .half) halfActive) (h.bindings.read (.inr .half) halfActive) :
        Eval context state (.variable (loopName (.inr .half)))
          (loopValue buffers start index step n 0 (.inr .half)) state)
  have stepE := mul_expr_eval context (h.parameter context .step)
    (Eval.literal (.integer 2 "ULL") _ (.integer (integer64 2)) (by rfl))
    bounds.2.2.1 (by norm_num) lb.2.2.1
  have startE : Eval context state
      (if right then addExpr (.variable "start") (.variable "half") else .variable "start")
      (.integer (integer64 (if right then start+half else start))) state := by
    cases right
    · exact h.parameter context .start
    · exact add_expr_eval context (h.parameter context .start) halfE bounds.1 lb.2.2.2.1 rb.1
  have indexE : Eval context state
      (if right then addExpr (.variable "index") (.variable "step") else .variable "index")
      (.integer (integer64 (if right then index+step else index))) state := by
    cases right
    · exact h.parameter context .index
    · exact add_expr_eval context (h.parameter context .index) (h.parameter context .step)
        bounds.2.1 bounds.2.2.1 rb.2.1
  refine .ordered (List.Perm.refl _) (.cons (h.parameter context .output) (.cons startE
    (.cons (h.parameter context .input) (.cons indexE (.cons stepE
    (.cons (h.parameter context .twiddle) (.cons halfE
    (.cons (h.parameter context .total) (.cons (h.parameter context .work) .nil))))))))) ?_
  exact .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl .nil))))))))

theorem arguments_call_free (right : Bool) : ∀e∈recursiveArguments right,SourcePure.CallFree e := by
  cases right <;> simp [recursiveArguments,SourcePure.CallFree,addExpr,mulExpr,literal]

#print axioms View.half_expr
#print axioms View.arguments_eval
#print axioms arguments_call_free
end Header
end RH080Next.FFTPV.RecursiveSource
