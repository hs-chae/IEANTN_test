/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoOutside
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DropTwoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

theorem source_drop_two_total {F : Type} (context : Context F)
    (programPinned : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program)
    (before : State F) (workObject previous : Nat) (ids : InitVar→Nat) (old : Nat→Nat) (well : WellScoped before)
    (params : Locals before (fun v=>name (lift v)) (fun v=>type (lift v)) ids before.scope
      (fun v=>values workObject old previous (lift v)))
    (array : WordArrayRep before workObject 512 old) (digits : ∀k,k<6 → old (192+k)<base) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      ((ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body).drop 26).take 6=statements ∧
      ((ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body).drop 26).take 6=statements ∧
      (∃after newId,ExecList context before statements .normal after ∧
      WordArrayRep after workObject 512 (roundData old 192) ∧
      Locals after name type (combinedIds ids newId) before.scope (values workObject old 4) ∧
      Frame before.nextObject before after [workObject,ids InitVar.i] ∧
      FFT.Limbs.magnitude base 6 (fun k=>roundData old 192 (192+k))=
        FFT.Limbs.ceilQuotient (FFT.Limbs.magnitude base 6 (fun k=>old (192+k))) (base^2) ∧
      (∀other flow,ExecList context before statements flow other → flow=.normal ∧ other=after)) := by
  have selected : findFunction context.program "increment_words"=some increment_words_ast:=by
    rcases programPinned with h|h <;> rw [h] <;> rfl
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,
    actual_six_statements,by rfl,drop_two_total context selected before workObject previous ids old well params array digits⟩

#print axioms source_drop_two_total
end RH080Next.FFTPV.DropTwoSource
