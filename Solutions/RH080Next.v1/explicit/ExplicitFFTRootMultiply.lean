/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootSetupValue
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)

def multiplyStatement (p : Param) (offset : Nat) (a : Param) (aOffset : Nat) (b : Param) (bOffset : Nat) : Stmt:=
  StatusCall.statement "fixed_multiply" [pointerExpr p offset,pointerExpr a aOffset,pointerExpr b bOffset,pointerExpr .work 36]

/-- Actual source multiply/status-assignment at arbitrary initializer slices.
The output relation, caller frame and untouched-word theorem all come from the
full source helper contract, including shared-object scratch refinement. -/
theorem multiply_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (incrementSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (canonicalSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before : State F} {input : Input} {owner statusId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ScaleView before input owner statusId ids data) (scope : owner≤ before.scope)
    (p : Param) (hp : PointerParam p) (offset : Nat) (a : Param) (ha : PointerParam a) (aOffset : Nat)
    (b : Param) (hb : PointerParam b) (bOffset : Nat) (aValue bValue : Int)
    (aRep : FixedValue data (pointerStart input a+aOffset) aValue)
    (bRep : FixedValue data (pointerStart input b+bOffset) bValue)
    (aSmall : aValue.natAbs≤1000*10^36) (bSmall : bValue.natAbs≤1000*10^36)
    (outBound : pointerStart input p+offset+6≤ input.layout.size)
    (aBound : pointerStart input a+aOffset+6≤ input.layout.size) (bBound : pointerStart input b+bOffset+6≤ input.layout.size)
    (aSeparate : pointerStart input a+aOffset+6≤ input.layout.workStart+36 ∨ input.layout.workStart+46≤ pointerStart input a+aOffset)
    (bSeparate : pointerStart input b+bOffset+6≤ input.layout.workStart+36 ∨ input.layout.workStart+46≤ pointerStart input b+bOffset)
    (outSeparate : pointerStart input p+offset+6≤ input.layout.workStart+36 ∨ input.layout.workStart+46≤ pointerStart input p+offset)
    (offset64 : offset<2^64) (aOffset64 : aOffset<2^64) (bOffset64 : bOffset<2^64) :
    ∃after nextData,Exec context before (multiplyStatement p offset a aOffset b bOffset) .normal after ∧
      Every context before (multiplyStatement p offset a aOffset b bOffset) .normal after ∧
      ScaleView after input owner statusId ids nextData ∧
      FixedValue nextData (pointerStart input p+offset) ((aValue*bValue)/FFT.IntegerModel.unit) ∧
      MultiplyCall.CallerFrame before after [input.layout.object,input.layout.object] ∧
      ∀k,k< input.layout.size → (k< pointerStart input p+offset ∨ pointerStart input p+offset+6≤ k) →
        (k< input.layout.workStart+36 ∨ input.layout.workStart+46≤ k) → nextData k=data k := by
  have workBound:=input.layout.workBound
  obtain ⟨after,nextData,called,post,math,normalized,sign,workWords,outWords,frame,every⟩:=MultiplyCall.fixed_multiply_correct_words context
    selected zeroSelected incrementSelected canonicalSelected before
    input.layout.object input.layout.size (pointerStart input p+offset)
    input.layout.object input.layout.size (pointerStart input a+aOffset)
    input.layout.object input.layout.size (pointerStart input b+bOffset)
    input.layout.object input.layout.size (input.layout.workStart+36)
    data data data data h.params.well h.params.array h.params.array h.params.array h.params.array
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    (Or.inr (by simpa [Nat.add_assoc] using aSeparate)) (Or.inr (by simpa [Nat.add_assoc] using bSeparate))
    (Or.inr (by simpa [Nat.add_assoc] using outSeparate)) outBound aBound bBound (by omega)
    aRep.digits bRep.digits aRep.sign bRep.sign (aRep.small aSmall) (bRep.small bSmall)
  have objects : ∀id,id< before.nextObject → id≠input.layout.object → after.objects id=before.objects id:=by
    intro id old separate;exact frame.frame.outside id old (by simp [separate])
  have view:=h.reframe post frame.environment scope frame.scope frame.frame.well objects
  have args : Args context before [pointerExpr p offset,pointerExpr a aOffset,pointerExpr b bOffset,pointerExpr .work 36]
      [.pointer (wordPointer input.layout.object (pointerStart input p+offset)),
       .pointer (wordPointer input.layout.object (pointerStart input a+aOffset)),
       .pointer (wordPointer input.layout.object (pointerStart input b+bOffset)),
       .pointer (wordPointer input.layout.object (input.layout.workStart+36))] before:=by
    apply Args.ordered (order:=[(0,pointerExpr p offset),(1,pointerExpr a aOffset),(2,pointerExpr b bOffset),(3,pointerExpr .work 36)])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object (pointerStart input p+offset))),
        (1,.pointer (wordPointer input.layout.object (pointerStart input a+aOffset))),
        (2,.pointer (wordPointer input.layout.object (pointerStart input b+bOffset))),
        (3,.pointer (wordPointer input.layout.object (input.layout.workStart+36)))])
    · exact List.Perm.refl _
    · exact .cons (pointer_eval context h.params p hp offset (by omega) offset64)
        (.cons (pointer_eval context h.params a ha aOffset (by omega) aOffset64)
          (.cons (pointer_eval context h.params b hb bOffset (by omega) bOffset64)
            (.cons (pointer_eval context h.params .work (Or.inr rfl) 36 (by simp only [pointerStart];omega) (by norm_num)) .nil)))
    · change List.Forall₂ _ [0,1,2,3] _;exact .cons rfl (.cons rfl (.cons rfl (.cons rfl .nil)))
  have run:=StatusCall.assignment_execution h.statusLookup view.statusLookup h.status view.status args called
  have output : FixedValue nextData (pointerStart input p+offset) ((aValue*bValue)/FFT.IntegerModel.unit):=by
    refine ⟨normalized,sign,?_⟩
    rw [aRep.represented,bRep.represented] at math
    exact math
  have everyStep : Every context before (multiplyStatement p offset a aOffset b bOffset) .normal after:=by
    intro other result observed
    apply StatusCall.assignment_every_execution h.statusLookup view.statusLookup h.status view.status
      (args:=args) (callee:=every) (run:=observed)
    intro expression member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> exact pointer_expr_pure _ _
  refine ⟨after,nextData,run,everyStep,view,output,frame,?_⟩
  intro k hk outside scratch
  exact outWords k hk outside (Or.inr (by simpa [Nat.add_assoc] using scratch))

#print axioms multiply_execution
end RH080Next.FFTPV.RootSource
