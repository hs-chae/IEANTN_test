/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTAnswerInitialization
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AnswerSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

def result (data : Nat→Nat) (allowance : Nat) : Nat:=computed (firstValue data) (secondValue data) sentinel allowance

theorem status_environment_scope {F : Type} {context : Context F} {before after : State F} {flow : Flow} {allowance : Nat}
    (run : Exec context before (statusBranch allowance) flow after) :
    after.environment=before.environment ∧ after.scope=before.scope := by
  cases run with
  | ifFalse evaluated truth=>
    have same:=SourcePure.eval_state evaluated (by trivial)
    cases same
    exact ⟨rfl,rfl⟩
  | ifTrue evaluated truth body=>
    have same:=SourcePure.eval_state evaluated (by trivial)
    cases same
    cases body with
    | block entered run finish=>subst_vars;exact ⟨rfl,rfl⟩

/-- The actual answer declaration and full guarded conversion block. All
mathematical outputs are computed from the actual unsigned source arrays;
no final numerical bound or successful application execution is assumed. -/
theorem answer_total {F : Type} (context : Context F)
    (selected : findFunction context.program "convert_bound"=some convert_bound_ast)
    (before : State F) (workObject allowance : Nat) (ids : InputVar→Nat) (data : Nat→Nat)
    (well : WellScoped before)
    (params : Locals before (fun v=>name (inputLift v)) (fun v=>type (inputLift v)) ids before.scope
      (fun v=>values workObject 0 0 0 (inputLift v)))
    (array : WordArrayRep before workObject 512 data) (separate : ∀v,workObject≠ids v)
    (totalDigits : ∀k,k<6 → data (192+k)<1000000000) (quadDigits : ∀k,k<6 → data (208+k)<1000000000)
    (budget : allowance≤615) :
    ∃after answerId,ExecList context before [answerDeclaration,statusBranch allowance] .normal after ∧
      Slot after answerId before.scope .u64 (.integer (integer64 (result data allowance))) ∧
      after.environment.lookup "answer"=some (scalarPointer answerId .u64) ∧
      after.scope=before.scope ∧ WordArrayRep after workObject 512 data ∧
      Frame before.nextObject before after [] ∧
      result data allowance<2^64 ∧
      (∀other flow,ExecList context before [answerDeclaration,statusBranch allowance] flow other → flow=.normal ∧ other=after) := by
  obtain ⟨initialized,answerId,declRun,initializedParams,initializedArray,declFrame,fresh,environment,declEvery⟩:=
    initialize_answer context before workObject ids data well params array separate
  have declScope : initialized.scope=before.scope:=by
    cases declRun with
    | declareSome evaluated declared=>
      have same:=SourcePure.eval_state evaluated (by trivial)
      cases same
      exact (SourceLocals.declare_frame declared).1
  have separate' : ∀v,workObject≠mainIds ids answerId v:=by
    have oldWork:=well.objectIds _ _ array.2.1
    intro v;cases v <;> simp only [mainIds] <;> first | exact separate _ | omega
  obtain ⟨after,guardRun,finalArray,finalParams,guardFrame,guardEvery⟩:=
    status_execution context selected initialized workObject before.scope sentinel allowance (mainIds ids answerId) data initializedParams initializedArray
      separate' declFrame.well (by norm_num [sentinel]) totalDigits quadDigits budget
  have narrow : Frame before.nextObject initialized after []:=by
    refine ⟨guardFrame.well,declFrame.fresh.trans guardFrame.nextObject,guardFrame.nextObject,guardFrame.nextScope,guardFrame.mode,guardFrame.foreign,?_⟩
    intro id old away
    exact guardFrame.outside id (lt_of_lt_of_le old declFrame.nextObject) (by simp only [List.mem_singleton,mainIds];omega)
  have run : ExecList context before [answerDeclaration,statusBranch allowance] .normal after:=.cons declRun (.cons guardRun .nil)
  refine ⟨after,answerId,run,finalParams.slots MainVar.answer,finalParams.lookup MainVar.answer,
    (status_environment_scope guardRun).2.trans declScope,finalArray,declFrame.trans narrow,
    computed_fits _ _ _ _ (by norm_num [sentinel]) budget,?_⟩
  intro other flow arbitrary
  cases arbitrary with
  | abrupt actual abnormal=>exact False.elim (abnormal (declEvery _ _ actual).1)
  | cons actual tail=>
    obtain ⟨_,eqs⟩:=declEvery _ _ actual
    cases eqs
    cases tail with
    | abrupt actual abnormal=>exact False.elim (abnormal (guardEvery _ _ actual).1)
    | cons actual tail=>
      obtain ⟨_,eqs⟩:=guardEvery _ _ actual
      cases eqs
      cases tail
      exact ⟨rfl,rfl⟩

private theorem computed_of_small (first second allowance prior : Nat)
    (small : first+second+allowance<1000000000000000000) :
    computed first second prior allowance=first+second+allowance := by
  unfold computed
  rw [if_pos (by dsimp [limit];omega),if_pos (by dsimp [limit];omega)]

/-- A pure range corollary, for later instantiation by independently checked
numerical receipts. The source theorem above also covers sentinel outcomes. -/
theorem result_of_small_sum (data : Nat→Nat) (allowance : Nat)
    (totalDigits : ∀k,k<6 → data (192+k)<1000000000) (quadDigits : ∀k,k<6 → data (208+k)<1000000000)
    (small : FFT.Limbs.magnitude 1000000000 6 (fun k=>data (192+k))+
      FFT.Limbs.magnitude 1000000000 6 (fun k=>data (208+k))+allowance<1000000000000000000) :
    result data allowance=FFT.Limbs.magnitude 1000000000 6 (fun k=>data (192+k))+
      FFT.Limbs.magnitude 1000000000 6 (fun k=>data (208+k))+allowance := by
  have small' : FFT.Limbs.magnitude ConvertBoundSource.base 6 (fun k=>data (192+k))+
      FFT.Limbs.magnitude ConvertBoundSource.base 6 (fun k=>data (208+k))+allowance<1000000000000000000 := by
    simpa only [ConvertBoundSource.base] using small
  have ht : FFT.Limbs.magnitude ConvertBoundSource.base 6 (fun k=>data (192+k))<ConvertBoundSource.base^2 := by
    norm_num [ConvertBoundSource.base] at small' ⊢
    omega
  have hq : FFT.Limbs.magnitude ConvertBoundSource.base 6 (fun k=>data (208+k))<ConvertBoundSource.base^2 := by
    norm_num [ConvertBoundSource.base] at small' ⊢
    omega
  have total:=(ConvertBoundSource.converted_magnitude data 192 totalDigits).trans (if_pos ht)
  have quad:=(ConvertBoundSource.converted_magnitude data 208 quadDigits).trans (if_pos hq)
  have exactValue : result data allowance=
      FFT.Limbs.magnitude ConvertBoundSource.base 6 (fun k=>data (192+k))+
        FFT.Limbs.magnitude ConvertBoundSource.base 6 (fun k=>data (208+k))+allowance :=
    (congrArg₂ (fun first second=>computed first second sentinel allowance) total quad).trans
      (computed_of_small _ _ _ _ small')
  simpa only [ConvertBoundSource.base] using exactValue

#print axioms answer_total
#print axioms result_of_small_sum
end RH080Next.FFTPV.AnswerSource
