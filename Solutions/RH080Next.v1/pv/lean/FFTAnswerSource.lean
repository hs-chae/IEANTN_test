/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTAnswerFinal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AnswerSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

def profileProgram (fap : Bool) : Program:=if fap then FapFFTRecursivePV.program else FFTRecursivePV.program
def profileBody (fap : Bool) : Stmt:=if fap then FapFFTRecursivePV.fap_recursive_norm_upper_ast.body else FFTRecursivePV.w4_recursive_norm_upper_ast.body
def profileAllowance (fap : Bool) : Nat:=if fap then 20 else 100

theorem actual_profile_answer (fap : Bool) :
    ((ProductRow.items (profileBody fap)).drop 39).take 2=[answerDeclaration,statusBranch (profileAllowance fap)] := by
  cases fap <;> rfl

theorem source_answer_total {F : Type} (context : Context F) (fap : Bool)
    (programPinned : context.program=profileProgram fap)
    (before : State F) (workObject : Nat) (ids : InputVar→Nat) (data : Nat→Nat)
    (well : WellScoped before)
    (params : Locals before (fun v=>name (inputLift v)) (fun v=>type (inputLift v)) ids before.scope
      (fun v=>values workObject 0 0 0 (inputLift v)))
    (array : WordArrayRep before workObject 512 data) (separate : ∀v,workObject≠ids v)
    (totalDigits : ∀k,k<6 → data (192+k)<1000000000) (quadDigits : ∀k,k<6 → data (208+k)<1000000000)
    :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      ((ProductRow.items (profileBody fap)).drop 39).take 2=[answerDeclaration,statusBranch (profileAllowance fap)] ∧
      (∃after answerId,ExecList context before [answerDeclaration,statusBranch (profileAllowance fap)] .normal after ∧
      Slot after answerId before.scope .u64 (.integer (integer64 (result data (profileAllowance fap)))) ∧
      after.environment.lookup "answer"=some (scalarPointer answerId .u64) ∧
      after.scope=before.scope ∧ WordArrayRep after workObject 512 data ∧
      Frame before.nextObject before after [] ∧
      result data (profileAllowance fap)<2^64 ∧
      (∀other flow,ExecList context before [answerDeclaration,statusBranch (profileAllowance fap)] flow other → flow=.normal ∧ other=after)) := by
  have selected : findFunction context.program "convert_bound"=some convert_bound_ast:=by
    rw [programPinned]
    cases fap <;> rfl
  have budget : profileAllowance fap≤615:=by cases fap <;> norm_num [profileAllowance]
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,actual_profile_answer fap,
    answer_total context selected before workObject (profileAllowance fap) ids data well params array separate totalDigits quadDigits budget⟩

#print axioms actual_profile_answer
#print axioms source_answer_total
end RH080Next.FFTPV.AnswerSource
