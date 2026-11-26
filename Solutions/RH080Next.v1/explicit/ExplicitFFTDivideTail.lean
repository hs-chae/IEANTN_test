/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTDivideRounding
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DivideSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def roundingFlow (old : Nat → Nat) (start n d ceiling : Nat) : Flow :=
  if 0 < ceiling ∧ 0 < (division old start n d 0).2 then .returned (.integer (integer64 0)) else .normal

/-- The genuine optional ceiling branch calls the already verified source
helper, preserving both nested block lifetimes and the outer function locals. -/
theorem rounding_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast)
    {before : State F} {object length start n d ceiling owner : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View before object length start n d ceiling owner li old 0) :
    ∃after,Exec context before roundingStatement (roundingFlow old start n d ceiling) after ∧
      WordArrayRep after object length (roundedData old start n d ceiling) ∧
      IncrementSource.FullCallerFrame before after object := by
  by_cases hc : 0 < ceiling
  · have ceilingTrue : (Value.integer (.boolean (decide (0 < ceiling)))).truth=some true := by
      simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hc]
    by_cases hr : 0 < (division old start n d 0).2
    · let outer:=before.enterScope
      let inner:=outer.enterScope
      have hi : View inner object length start n d ceiling owner li old 0:=h.enter.enter
      obtain ⟨middle,called,rep,frame⟩:=IncrementSource.increment_words_call_framed context selected inner
        object length start n (currentData old start n d 0) hi.well hi.array h.bound h.small (quotient_digits h)
      have noCarry:=rounded_increment_carry_zero h hr
      rw [noCarry] at called
      have args : Args context inner [.variable "a",.variable "n"]
          [.pointer (wordPointer object start),.integer (integer64 n)] inner := by
        apply Args.ordered (order:=[(0,.variable "a"),(1,.variable "n")])
          (evaluated:=[(0,.pointer (wordPointer object start)),(1,.integer (integer64 n))])
        · exact List.Perm.refl _
        · exact .cons (.variable (hi.locals.lookup Var.a) (hi.locals.read Var.a))
            (.cons (.variable (hi.locals.lookup Var.n) (hi.locals.read Var.n)) .nil)
        · change List.Forall₂ _ [0,1] _
          exact .cons rfl (.cons rfl .nil)
      let afterInner : State F:={middle.leaveScope outer.nextScope outer.environment with scope:=outer.scope}
      have innerRun : Exec context outer (.block [incrementStatement]) (.returned (.integer (integer64 0))) afterInner :=
        .block (by rfl) (.abrupt (.returnSome (.call args called)) (by simp)) (by rfl)
      have innerFrame : IncrementSource.FullCallerFrame outer afterInner object:=close_full_frame h.enter.well frame
      have innerRep : WordArrayRep afterInner object length
          (IncrementSource.currentData (currentData old start n d 0) start n):=IncrementSource.wordArray_leave rep
      have remainderTrue : (Value.integer (.boolean (decide (0 < (division old start n d 0).2)))).truth=some true := by
        simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hr]
      have ifRun : Exec context outer remainderBranch (.returned (.integer (integer64 0))) afterInner :=
        .ifTrue (remainder_eval context h.enter) remainderTrue innerRun
      let after : State F:={afterInner.leaveScope before.nextScope before.environment with scope:=before.scope}
      have outerRun : Exec context before (.block [remainderBranch]) (.returned (.integer (integer64 0))) after :=
        .block (by rfl) (.abrupt ifRun (by simp)) (by rfl)
      refine ⟨after,?_,?_,close_full_frame h.well innerFrame⟩
      · simpa only [roundingStatement,roundingFlow,if_pos (And.intro hc hr)] using
          Exec.ifTrue (ceiling_eval context h) ceilingTrue outerRun
      · simpa only [roundedData,if_pos (And.intro hc hr)] using IncrementSource.wordArray_leave innerRep
    · let after : State F:={before.enterScope.leaveScope before.nextScope before.environment with scope:=before.scope}
      have ifRun : Exec context before.enterScope remainderBranch .normal before.enterScope :=
        .ifFalse (remainder_eval context h.enter)
          (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hr])
      have outerRun : Exec context before (.block [remainderBranch]) .normal after :=
        .block (by rfl) (.cons ifRun .nil) (by rfl)
      refine ⟨after,?_,?_,close_full_frame h.well (full_frame_refl object h.enter.well)⟩
      · simpa only [roundingStatement,roundingFlow,if_neg (show ¬(0 < ceiling ∧ 0 < (division old start n d 0).2) by simp [hr])] using
          Exec.ifTrue (ceiling_eval context h) ceilingTrue outerRun
      · simpa only [roundedData,if_neg (show ¬(0 < ceiling ∧ 0 < (division old start n d 0).2) by simp [hr])] using
          IncrementSource.wordArray_leave h.enter.array
  · refine ⟨before,?_,?_,full_frame_refl object h.well⟩
    · simpa only [roundingStatement,roundingFlow,if_neg (show ¬(0 < ceiling ∧ 0 < (division old start n d 0).2) by simp [hc])] using
        Exec.ifFalse (ceiling_eval context h) (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hc])
    · simpa [roundedData,hc] using h.array

#print axioms rounding_execution
end RH080Next.FFTPV.DivideSource
