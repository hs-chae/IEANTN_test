/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTOutputSumLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.OutputSumSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

theorem source_loop_execution {F : Type} (context : Context F)
    (programPinned : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program) (steps : Nat)
    {before : State F} {outputObject workObject n owner i : Nat}
    {ids : Var→Nat} {outputData workData : Nat→Nat} {samples : Nat→FFT.IntegerModel.CInt}
    (h : View before outputObject workObject n ids owner i outputData workData samples) (remaining : i+steps=n) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[25]?=some loop ∧
      (ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body)[25]?=some loop ∧
      (∃after nextWork,Exec context before loop .normal after ∧
      View after outputObject workObject n ids owner n outputData nextWork samples ∧
      Frame before.nextObject before after [workObject,ids Var.i] ∧
      (∀k,(k<192 ∨ 198≤k) → nextWork k=workData k) ∧
      (∀other flow,Exec context before loop flow other → flow=.normal ∧ other=after)) := by
  have selected : findFunction context.program "add_magnitude"=some add_magnitude_ast:=by
    rcases programPinned with h|h <;> rw [h] <;> rfl
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,
    actual_w4_loop,actual_fap_loop,loop_execution context selected steps h remaining⟩

#print axioms source_loop_execution
end RH080Next.FFTPV.OutputSumSource
