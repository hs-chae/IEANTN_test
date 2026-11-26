/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTProductAllExecutions
import FFTRecursiveSource
import FapFFTRecursiveSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductOuter
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open ApplicationBirthFrame

theorem recursive_core_actual : (ProductRow.items FFTRecursivePV.fixed_multiply_ast.body).getD 2 (.block [])=outerLoop:=by rfl
theorem fap_recursive_core_actual : (ProductRow.items FapFFTRecursivePV.fixed_multiply_ast.body).getD 2 (.block [])=outerLoop:=by rfl

/-- Complete termination and universal correctness contract of the actual
nested multiplication core. Initialization and the function suffix are separate
obligations; this contract deliberately makes neither a successful-effects nor
an intended-output assumption. -/
def CoreContract {F : Type} (context : Context F) (before : State F)
    (aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat)
    (ids owners : PVar→Nat) (a b : Nat→Nat) : Prop :=
  (∃after,Exec context before outerLoop .normal after) ∧
  (∀after flow,Exec context before outerLoop flow after → flow=.normal ∧ ∃finalData,
    View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b finalData 5 ∧
    Frame before.nextObject before after [workObj,ids PVar.i] ∧
    RH080Next.FFT.Limbs.value 1000000000 10 (fun k=>finalData (workStart+k))=
      RH080Next.FFT.Limbs.value 1000000000 5 a*RH080Next.FFT.Limbs.value 1000000000 5 b)

/-- Actual C characters have independently specified syntactic correspondence
to the actual AST, and that AST's multiplication core terminates and is correct
for every execution. Both original Fap and w4 physical source files are covered.
This verifies the core only; it does not claim a complete helper/FFT PV theorem. -/
theorem source_product_core_total {F : Type} (context : Context F) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat}
    {ids owners : PVar→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data 0)
    (initialized : ∀k,k<10 → data (workStart+k)=0) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
    Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
    (ProductRow.items FFTRecursivePV.fixed_multiply_ast.body).getD 2 (.block [])=outerLoop ∧
    (ProductRow.items FapFFTRecursivePV.fixed_multiply_ast.body).getD 2 (.block [])=outerLoop ∧
    CoreContract context before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b := by
  obtain ⟨after,finalData,run,ha,frame,product⟩:=source_product_core context h initialized
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,
    recursive_core_actual,fap_recursive_core_actual,⟨after,run⟩,
    fun after flow run=>every_source_product_core h initialized run⟩

#print axioms recursive_core_actual
#print axioms fap_recursive_core_actual
#print axioms source_product_core_total
end RH080Next.FFTPV.ProductOuter
