/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleCertificateBridge
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.TwiddleSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

theorem source_construct_table {F : Type} (context : Context F)
    (programPinned : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program) (before : State F)
    (tableObject workObject n : Nat) (oldIds : InitVar→Nat) (workData : Nat→Nat)
    (original : n=131072 ∨ n=16777216) (well : WellScoped before)
    (locals : Locals before (fun v=>name (lift v)) (fun v=>type (lift v)) oldIds before.scope
      (fun v=>values tableObject workObject n 0 (lift v)))
    (table : WordArrayRep before tableObject (n/2*12) (fun _=>0))
    (work : WordArrayRep before workObject 512 workData) (different : tableObject≠workObject)
    (rootDigits : ∀c : Fin 2,∀d,d<5 → workData (128+6*c.val+d)<1000000000)
    (rootSigns : ∀c : Fin 2,workData (128+6*c.val+5)≤1)
    (rootValue : ComplexSource.pair workData 128=FFT.IntegerModel.root n) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[17]?=some unitAssignment ∧
      (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[18]?=some jDeclaration ∧
      (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[19]?=some loop ∧
      (ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body)[19]?=some loop ∧
      (∃after newId tableData finalWork,
      ExecList context before [unitAssignment,jDeclaration,loop] .normal after ∧
      View after tableObject workObject n (combinedIds oldIds newId) before.scope (n/2) tableData finalWork (FFT.IntegerModel.root n) ∧
      Frame before.nextObject before after [tableObject,workObject] ∧
      (∀k,k<512 →46≤k → finalWork k=workData k) ∧
      (∀other flow,ExecList context before [unitAssignment,jDeclaration,loop] flow other → flow=.normal ∧ other=after)) := by
  have functions : Functions context := by
    constructor <;> (rcases programPinned with h|h <;> rw [h] <;> rfl)
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,
    actual_unit_assignment,actual_j_declaration,actual_w4_loop,actual_fap_loop,
    construct_table context functions before tableObject workObject n oldIds workData original well locals table work different rootDigits rootSigns rootValue⟩

#print axioms source_construct_table
end RH080Next.FFTPV.TwiddleSource
