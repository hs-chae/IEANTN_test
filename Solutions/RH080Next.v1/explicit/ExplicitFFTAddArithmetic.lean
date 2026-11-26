/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddSubBranch
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def rawData (input : Input) : Nat → Nat:=
  if input.asign=input.bsign then signedData input false false input.asign
  else signedData input true (decide (input.cmp=0)) input.subtractionSign
def rawStatus (input : Input) : Nat:=
  if input.asign=input.bsign then (scan false (input.left false) (input.right false) 5).2 else 0

structure ArithmeticView {F : Type} (state : State F) (input : Input) (owner : Nat) (li : Var → Nat) : Prop where
  array : WordArrayRep state (input.layout.object .out) (input.layout.length (input.layout.object .out)) (rawData input)
  locals : Locals state name type li owner (values input 5 (rawStatus input))
  separate : ∀v,input.layout.object .out≠li v
  well : WellScoped state

theorem same_sign_eval {F : Type} (context : Context F) {state : State F} {input : Input} {sub swap : Bool}
    {owner j : Nat} {li : Var → Nat} (h : View state input sub swap owner li j) :
    Eval context state sameSignTest (.integer (.boolean (decide (input.asign=input.bsign)))) state:=
  .binaryLR (.variable (h.locals.lookup Var.asign) (h.locals.read Var.asign))
    (.variable (h.locals.lookup Var.bsign) (h.locals.read Var.bsign))
    (by simp only [values,binary,binary64_eq input.asign input.bsign
      (lt_of_le_of_lt input.signA (by norm_num)) (lt_of_le_of_lt input.bsign_bound (by norm_num)),Option.map_some])

/-- Source dispatch consumes the actual stored sign comparison; both
possible arithmetic branches have their complete in-place source proofs. -/
theorem arithmetic_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner : Nat} {li : Var → Nat} (h : ∀sub swap,View before input sub swap owner li 0) :
    ∃after,Exec context before arithmeticBranch .normal after ∧ ArithmeticView after input owner li ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes input li) := by
  by_cases hs : input.asign=input.bsign
  · obtain ⟨after,run,post,frame⟩:=add_branch_execution context (h false false)
    refine ⟨after,.ifTrue (same_sign_eval context (h false false)) ?_ run,?_,frame⟩
    · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hs]
    · exact ⟨by simpa only [rawData,if_pos hs] using post.array,
        by simpa only [rawStatus,if_pos hs] using post.locals,post.separate,post.well⟩
  · obtain ⟨after,run,post,frame⟩:=sub_branch_execution context (h true (decide (input.cmp=0)))
    refine ⟨after,.ifElse (same_sign_eval context (h true (decide (input.cmp=0)))) ?_ run,?_,frame⟩
    · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hs]
    · exact ⟨by simpa only [rawData,if_neg hs] using post.array,
        by simpa only [rawStatus,if_neg hs] using post.locals,post.separate,post.well⟩

theorem signedData_digit (input : Input) (sub swap : Bool) (sign i : Nat) (hi : i < 5) :
    signedData input sub swap sign (input.layout.start .out+i)=
      (scan sub (input.left swap) (input.right swap) 5).1 i := by
  simp [signedData,Function.update_of_ne (show input.layout.start .out+i≠input.layout.start .out+5 by omega),
    currentData,show input.layout.start .out ≤ input.layout.start .out+i ∧ input.layout.start .out+i < input.layout.start .out+5 by omega]

theorem rawData_digits (input : Input) : ∀i < 5,rawData input (input.layout.start .out+i) < base := by
  intro i hi
  unfold rawData
  split_ifs
  all_goals
    rw [signedData_digit input _ _ _ i hi]
    exact (scan_bounds _ _ _ 5 (input.left_bound _) (input.right_bound _)).2 i hi

theorem rawStatus_bound (input : Input) : rawStatus input ≤ 1 := by
  unfold rawStatus
  split_ifs
  · exact (scan_bounds false _ _ 5 (input.left_bound false) (input.right_bound false)).1
  · norm_num

theorem arithmetic_scope {F : Type} {context : Context F} {before after : State F} {flow : Flow}
    (run : Exec context before arithmeticBranch flow after) :
    after.environment=before.environment ∧ after.scope=before.scope := by
  cases run with
  | ifTrue ev tr body=>
    have same:=SourcePure.eval_state ev (by simp [sameSignTest,SourcePure.CallFree])
    subst_vars
    exact ApplicationLoopScope.block_fields body
  | ifElse ev tr body=>
    have same:=SourcePure.eval_state ev (by simp [sameSignTest,SourcePure.CallFree])
    subst_vars
    exact ApplicationLoopScope.block_fields body

#print axioms arithmetic_execution
#print axioms rawData_digits
#print axioms rawStatus_bound
end RH080Next.FFTPV.AddSource
