/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTNormalizeQuad
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.NormalizeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

def profileProgram (fap : Bool) : Program:=if fap then FapFFTRecursivePV.program else FFTRecursivePV.program
def profileBody (fap : Bool) : Stmt:=if fap then FapFFTRecursivePV.fap_recursive_norm_upper_ast.body else FFTRecursivePV.w4_recursive_norm_upper_ast.body

theorem actual_total_sequence (fap : Bool) : ((ProductRow.items (profileBody fap)).drop 32).take (if fap then 1 else 2)=totalStatements fap:=by cases fap <;> rfl

theorem actual_quad_sequence (fap : Bool) : ((ProductRow.items (profileBody fap)).drop 36).take 3=quadStatements:=by cases fap <;> rfl

theorem source_total_execution {F : Type} (context : Context F) (fap : Bool)
    (programPinned : context.program=profileProgram fap)
    {before : State F} {workObject n owner : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (params : Locals before name type ids owner (values workObject n))
    (array : WordArrayRep before workObject 512 old) (separate : ∀v,workObject≠ids v) (well : WellScoped before)
    (positive : 0<n) (small : n<1000000000) (digits : ∀k,k<6 → old (192+k)<1000000000) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      (((ProductRow.items (profileBody fap)).drop 32).take (if fap then 1 else 2)=totalStatements fap) ∧
      (∃after dataAfter,ExecList context before (totalStatements fap) .normal after ∧
      WordArrayRep after workObject 512 dataAfter ∧
      Locals after name type ids owner (values workObject n) ∧
      MultiplyCall.CallerFrame before after [workObject] ∧
      FFT.Limbs.magnitude 1000000000 6 (fun k=>dataAfter (192+k))=
        totalValue fap (FFT.Limbs.magnitude 1000000000 6 (fun k=>old (192+k))) n ∧
      (∀k,k<6 → dataAfter (192+k)<1000000000) ∧
      (∀k,(k<192 ∨ 198≤k) → dataAfter k=old k) ∧
      (∀other flow,ExecList context before (totalStatements fap) flow other → flow=.normal ∧ other=after)) := by
  have selected : findFunction context.program "divide_small"=some divide_small_ast:=by rw [programPinned];cases fap <;> rfl
  have increment : findFunction context.program "increment_words"=some increment_words_ast:=by rw [programPinned];cases fap <;> rfl
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,actual_total_sequence fap,
    total_execution context selected increment fap params array separate well positive small digits⟩

theorem source_quad_execution {F : Type} (context : Context F) (fap : Bool) 
    (programPinned : context.program=profileProgram fap)
    {before : State F} {workObject n owner : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (params : Locals before name type ids owner (values workObject n))
    (array : WordArrayRep before workObject 512 old) (separate : ∀v,workObject≠ids v) (well : WellScoped before)
    (positive : 0<n) (small : n<1000000000) (digits : ∀k,k<6 → old (208+k)<1000000000) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      (((ProductRow.items (profileBody fap)).drop 36).take 3=quadStatements) ∧
      (∃after dataAfter,ExecList context before quadStatements .normal after ∧
      WordArrayRep after workObject 512 dataAfter ∧
      Locals after name type ids owner (values workObject n) ∧
      MultiplyCall.CallerFrame before after [workObject] ∧
      FFT.Limbs.magnitude 1000000000 6 (fun k=>dataAfter (208+k))=
        quadValue (FFT.Limbs.magnitude 1000000000 6 (fun k=>old (208+k))) n ∧
      (∀k,k<6 → dataAfter (208+k)<1000000000) ∧
      (∀k,(k<208 ∨ 214≤k) → dataAfter k=old k) ∧
      (∀other flow,ExecList context before quadStatements flow other → flow=.normal ∧ other=after)) := by
  have selected : findFunction context.program "divide_small"=some divide_small_ast:=by rw [programPinned];cases fap <;> rfl
  have increment : findFunction context.program "increment_words"=some increment_words_ast:=by rw [programPinned];cases fap <;> rfl
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,actual_quad_sequence fap,
    quad_execution context selected increment params array separate well positive small digits⟩

#print axioms source_total_execution
#print axioms source_quad_execution
end RH080Next.FFTPV.NormalizeSource
