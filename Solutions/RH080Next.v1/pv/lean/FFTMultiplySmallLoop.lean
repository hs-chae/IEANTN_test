/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMultiplySmallBody
import ExplicitFFTCompareDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySmallSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs

theorem frame_restrict {F : Type} {a b : State F} {cutoff small : Nat} {written : List Nat}
    (h : ApplicationBirthFrame.Frame cutoff a b written) (le : small ≤ cutoff) :
    ApplicationBirthFrame.Frame small a b written :=
  ⟨h.well,le.trans h.fresh,h.nextObject,h.nextScope,h.mode,h.foreign,
    fun i hi absent=>h.outside i (lt_of_lt_of_le hi le) absent⟩

/-- The full actual forward loop terminates for every supported input length,
retaining exact data outside the target slice and every other old allocation. -/
theorem loop_execution {F : Type} (context : Context F) (remaining : Nat) {before : State F}
    {object length start n factor owner j : Nat} {li : Var → Nat} {old : Nat → Nat}
    (count : j+remaining=n) (h : View before object length start n factor owner li old j) :
    ∃after,Exec context before loop .normal after ∧
      View after object length start n factor owner li old n ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes object li) := by
  induction remaining generalizing before j with
  | zero =>
    have hj : j=n := by omega
    subst j
    refine ⟨before,.whileFalse (condition_eval context h) ?_,h,
      ApplicationBirthFrame.Frame.refl _ _ h.well (le_refl _)⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed]
  | succ r ih =>
    have hj : j < n := by omega
    obtain ⟨middle,body,hm,first⟩:=loop_body_execution context h hj
    obtain ⟨after,rest,ha,last⟩:=ih (by omega) hm
    have last':=frame_restrict last first.nextObject
    refine ⟨after,.whileNext (condition_eval context h) ?_ body rest,ha,first.trans last'⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj]

theorem actual_body_unique {F : Type} (context : Context F) : CompareSource.Unique context loopBody := by
  apply CompareSource.block_unique
  intro stmt member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    exact fun first second=>PureDeterminism.simple_unique
      (by simp [PureDeterminism.Simple,SourcePure.CallFree,tExpr,digitStmt,carryStmt,advanceStmt]) first second

theorem actual_loop_unique {F : Type} (context : Context F) : CompareSource.Unique context loop :=
  CompareSource.while_unique (by simp [condition,SourcePure.CallFree]) (actual_body_unique context)

#print axioms loop_execution
#print axioms actual_body_unique
#print axioms actual_loop_unique
end RH080Next.FFTPV.MultiplySmallSource
