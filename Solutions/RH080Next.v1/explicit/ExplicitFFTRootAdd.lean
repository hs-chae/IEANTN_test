/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootDivide
import ExplicitFFTAddSlice
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)
open FFT.Limbs

def addStatement (p : Param) (offset : Nat) (q : Param) (qOffset : Nat) (subtract : Expr) : Stmt:=
  StatusCall.statement "fixed_add" [pointerExpr p offset,pointerExpr p offset,pointerExpr q qOffset,subtract]

/-- Actual in-place source addition/subtraction, with its zero return proved
from the represented input magnitudes. The mathematical addition proof and all
source execution/lifetime/aliasing contracts are genuinely consumed. -/
theorem add_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_add"=some fixed_add_ast)
    (compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (canonicalSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before : State F} {input : Input} {owner statusId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ScaleView before input owner statusId ids data) (scope : owner≤ before.scope)
    (p : Param) (hp : PointerParam p) (offset : Nat) (q : Param) (hq : PointerParam q) (qOffset flag : Nat)
    (expression : Expr) (read : Eval context before expression (.integer (integer64 flag)) before)
    (expressionPure : SourcePure.CallFree expression)
    (flagBound : flag≤1) (aValue bValue : Int)
    (aRep : FixedValue data (pointerStart input p+offset) aValue)
    (bRep : FixedValue data (pointerStart input q+qOffset) bValue)
    (sumSmall : aValue.natAbs+bValue.natAbs< base^5)
    (bound : pointerStart input p+offset+6≤ input.layout.size)
    (qBound : pointerStart input q+qOffset+6≤ input.layout.size)
    (ranges : pointerStart input p+offset=pointerStart input q+qOffset ∨
      pointerStart input p+offset+6≤ pointerStart input q+qOffset ∨
      pointerStart input q+qOffset+6≤ pointerStart input p+offset)
    (offset64 : offset<2^64) (qOffset64 : qOffset<2^64) :
    ∃after nextData,Exec context before (addStatement p offset q qOffset expression) .normal after ∧
      Every context before (addStatement p offset q qOffset expression) .normal after ∧
      ScaleView after input owner statusId ids nextData ∧
      FixedValue nextData (pointerStart input p+offset) (if 0< flag then aValue-bValue else aValue+bValue) ∧
      IncrementSource.FullCallerFrame before after input.layout.object ∧
      ∀k,(k< pointerStart input p+offset ∨ pointerStart input p+offset+6≤ k) → nextData k=data k := by
  let layout : AddSource.Layout:=
    {object:=fun _=>input.layout.object,length:=fun _=>input.layout.size,
     start:=fun r=>match r with | .out | .a=>pointerStart input p+offset | .b=>pointerStart input q+qOffset,
     bound:=by intro r;cases r <;> assumption,
     safeA:=Or.inr (Or.inl rfl),safeB:=Or.inr ranges}
  let addition : AddSource.Input:=
    {layout:=layout,old:=fun _=>data,subtract:=flag,subtract_bound:=flagBound,
      digitsA:=aRep.digits,digitsB:=bRep.digits,signA:=aRep.sign,signB:=bRep.sign}
  have reps : ∀r,WordArrayRep before (addition.layout.object r) (addition.layout.length (addition.layout.object r)) (addition.old (addition.layout.object r)):=fun _=>h.params.array
  have magnitudeA : magnitude base 5 addition.a=aValue.natAbs:=by
    exact (represented_natAbs _ _).symm.trans (congrArg Int.natAbs aRep.represented)
  have magnitudeB : magnitude base 5 addition.b=bValue.natAbs:=by
    exact (represented_natAbs _ _).symm.trans (congrArg Int.natAbs bRep.represented)
  have zero : AddSource.rawStatus addition=0:=AddSource.rawStatus_zero_of_sum_lt addition (by rwa [magnitudeA,magnitudeB])
  obtain ⟨⟨after,called,post,frame,every⟩,statusBound,normalized,sign,math⟩:=AddSource.fixed_add_total context selected compareSelected canonicalSelected before addition h.params.well reps
  rw [zero] at called
  have view:=h.reframe post frame.environment scope frame.scope frame.well frame.objects
  have args : Args context before [pointerExpr p offset,pointerExpr p offset,pointerExpr q qOffset,expression]
      [.pointer (wordPointer input.layout.object (pointerStart input p+offset)),
       .pointer (wordPointer input.layout.object (pointerStart input p+offset)),
       .pointer (wordPointer input.layout.object (pointerStart input q+qOffset)),.integer (integer64 flag)] before:=by
    apply Args.ordered (order:=[(0,pointerExpr p offset),(1,pointerExpr p offset),(2,pointerExpr q qOffset),(3,expression)])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object (pointerStart input p+offset))),
        (1,.pointer (wordPointer input.layout.object (pointerStart input p+offset))),
        (2,.pointer (wordPointer input.layout.object (pointerStart input q+qOffset))),(3,.integer (integer64 flag))])
    · exact List.Perm.refl _
    · exact .cons (pointer_eval context h.params p hp offset (by omega) offset64)
        (.cons (pointer_eval context h.params p hp offset (by omega) offset64)
          (.cons (pointer_eval context h.params q hq qOffset (by omega) qOffset64) (.cons read .nil)))
    · change List.Forall₂ _ [0,1,2,3] _;exact .cons rfl (.cons rfl (.cons rfl (.cons rfl .nil)))
  have run:=StatusCall.assignment_execution h.statusLookup view.statusLookup h.status view.status args called
  have output : FixedValue (AddSource.finalData addition) (pointerStart input p+offset)
      (if 0< flag then aValue-bValue else aValue+bValue):=by
    refine ⟨normalized,sign,?_⟩
    have result:=math zero
    change CanonicalSource.represented _ (pointerStart input p+offset)=
      if 0< flag then CanonicalSource.represented data (pointerStart input p+offset)-CanonicalSource.represented data (pointerStart input q+qOffset)
      else CanonicalSource.represented data (pointerStart input p+offset)+CanonicalSource.represented data (pointerStart input q+qOffset) at result
    rwa [aRep.represented,bRep.represented] at result
  have everyStep : Every context before (addStatement p offset q qOffset expression) .normal after:=by
    intro other result observed
    apply StatusCall.assignment_every_execution h.statusLookup view.statusLookup h.status view.status (args:=args)
      (callee:=fun state result actual=>by simpa only [zero] using every state result actual) (run:=observed)
    intro e member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact pointer_expr_pure _ _
    · exact pointer_expr_pure _ _
    · exact pointer_expr_pure _ _
    · exact expressionPure
  refine ⟨after,AddSource.finalData addition,run,everyStep,view,output,frame,?_⟩
  intro k outside
  exact AddSource.finalData_outside addition k outside

#print axioms add_execution
end RH080Next.FFTPV.RootSource
