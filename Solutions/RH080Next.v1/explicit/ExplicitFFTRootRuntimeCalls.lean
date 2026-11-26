/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootTracking
import FFTRecursiveCopyFrame
import FFTCopyDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

structure Functions {F : Type} (context : Context F) : Prop where
  zero : findFunction context.program "zero_words"=some zero_words_ast
  copy : findFunction context.program "copy_words"=some copy_words_ast
  increment : findFunction context.program "increment_words"=some increment_words_ast
  divide : findFunction context.program "divide_small"=some divide_small_ast
  multiplySmall : findFunction context.program "multiply_small"=some multiply_small_ast
  multiply : findFunction context.program "fixed_multiply"=some fixed_multiply_ast
  compare : findFunction context.program "magnitude_compare"=some magnitude_compare_ast
  add : findFunction context.program "fixed_add"=some fixed_add_ast
  canonical : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast

theorem Runtime.after_unary {F : Type} {before after : State F} {input : Input}
    {owner statusId indexId index : Nat} {ids : Param → Nat} {old data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids old index)
    (view : ScaleView after input owner statusId ids data)
    (frame : IncrementSource.FullCallerFrame before after input.layout.object) :
    Runtime after input owner statusId indexId ids data index:=
  h.reframe view frame.environment frame.scope frame.objects

theorem Runtime.after_multiply {F : Type} {before after : State F} {input : Input}
    {owner statusId indexId index : Nat} {ids : Param → Nat} {old data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids old index)
    (view : ScaleView after input owner statusId ids data)
    (frame : MultiplyCall.CallerFrame before after [input.layout.object,input.layout.object]) :
    Runtime after input owner statusId indexId ids data index := by
  apply h.reframe view frame.environment frame.scope
  intro id old separate
  exact frame.frame.outside id old (by simp [separate])

theorem Runtime.after_copy {F : Type} {before after : State F} {input : Input}
    {owner statusId indexId index : Nat} {ids : Param → Nat} {old data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids old index)
    (view : ScaleView after input owner statusId ids data)
    (frame : CopyLoop.CallerFrame before after input.layout.object) :
    Runtime after input owner statusId indexId ids data index:=
  h.reframe view frame.environment frame.scope frame.objects

/-- Actual copy instruction retaining the live i slot through the callee's
proved frame. This source step is applicable inside the real while-body block. -/
theorem runtime_copy_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "copy_words"=some copy_words_ast)
    {before : State F} {input : Input} {owner statusId indexId index : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data index)
    (p : Param) (hp : PointerParam p) (offset : Nat) (q : Param) (hq : PointerParam q) (inputOffset : Nat)
    (bound : pointerStart input p+offset+6≤ input.layout.size) (inputBound : pointerStart input q+inputOffset+6≤ input.layout.size)
    (ranges : pointerStart input p+offset=pointerStart input q+inputOffset ∨
      pointerStart input p+offset+6≤ pointerStart input q+inputOffset ∨
      pointerStart input q+inputOffset+6≤ pointerStart input p+offset)
    (offset64 : offset<2^64) (inputOffset64 : inputOffset<2^64) :
    ∃after,Exec context before (copySliceStatement p offset q inputOffset) .normal after ∧
      Every context before (copySliceStatement p offset q inputOffset) .normal after ∧
      Runtime after input owner statusId indexId ids (CopyLoop.prefixData data
        (fun i=>data (pointerStart input q+inputOffset+i)) (pointerStart input p+offset) 6) index ∧
      CopyLoop.CallerFrame before after input.layout.object ∧
      ApplicationBirthFrame.Frame before.nextObject before after [input.layout.object] := by
  obtain ⟨after,called,post,readSource,frame,fullFrame⟩:=CopyLoop.copy_words_call_framed context selected before
    input.layout.object input.layout.size (pointerStart input p+offset)
    input.layout.object input.layout.size (pointerStart input q+inputOffset) 6 data data
    h.view.params.well h.view.params.array h.view.params.array (fun _=>rfl) (Or.inr ranges) bound inputBound (by norm_num)
  have args : Args context before [pointerExpr p offset,pointerExpr q inputOffset,.literal (.integer 6 "ULL")]
      [.pointer (wordPointer input.layout.object (pointerStart input p+offset)),
       .pointer (wordPointer input.layout.object (pointerStart input q+inputOffset)),.integer (integer64 6)] before:=by
    apply Args.ordered (order:=[(0,pointerExpr p offset),(1,pointerExpr q inputOffset),(2,.literal (.integer 6 "ULL"))])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object (pointerStart input p+offset))),
        (1,.pointer (wordPointer input.layout.object (pointerStart input q+inputOffset))),(2,.integer (integer64 6))])
    · exact List.Perm.refl _
    · exact .cons (pointer_eval context h.view.params p hp offset (by omega) offset64)
        (.cons (pointer_eval context h.view.params q hq inputOffset (by omega) inputOffset64)
          (.cons (.literal (.integer 6 "ULL") _ (.integer (integer64 6)) (by rfl)) .nil))
    · change List.Forall₂ _ [0,1,2] _;exact .cons rfl (.cons rfl (.cons rfl .nil))
  have view:=h.view.reframe post frame.environment h.active frame.scope frame.well frame.objects
  have everyStep:=every_expression_call (args:=args)
    (callee:=fun state output actual=>CopyLoop.call_unique selected called actual)
    (by intro e member;simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl|rfl
        · exact pointer_expr_pure _ _
        · exact pointer_expr_pure _ _
        · trivial)
  exact ⟨after,.expression (.call args called),everyStep,h.after_copy view frame,frame,fullFrame⟩

#print axioms Runtime.after_multiply
#print axioms runtime_copy_execution
end RH080Next.FFTPV.RootSource
