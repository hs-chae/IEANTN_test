/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddMagnitudeCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddMagnitudeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals
open FFT.Limbs

theorem final_normalized (input : Input) (k : Nat) (hk : k< input.layout.n) :
    currentData input input.layout.n (input.layout.outStart+k)<base:=by
  rw [currentData_processed input _ k hk]
  exact (AddSource.addDigits_bounds _ _ input.layout.n input.outDigits (fun j _=>aDigit_bound input j)).2 k hk

theorem zero_status_of_small (input : Input)
    (small : magnitude base input.layout.n (fun j=>input.old input.layout.outObject (input.layout.outStart+j))+
      magnitude base input.layout.n (aDigit input)<base^input.layout.n) :
    (row input input.layout.n).2=0:=
  (addDigits_no_overflow base input.layout.n (by norm_num [base]) _ _ small).1

/-- Output arrays may share one allocation with their read-only input slice;
only the exact output n words change. All initializations, overflow status,
source's cutoff at five input magnitude words, and final integer conservation
are proved from the actual source. -/
def Correct {F : Type} (context : Context F) (before : State F) (input : Input) : Prop:=
  (∃after,Call context "add_magnitude" (arguments input) before (.value (.integer (integer64 (row input input.layout.n).2))) after ∧
    RootSource.EveryCall context before "add_magnitude" (arguments input) (.value (.integer (integer64 (row input input.layout.n).2))) after ∧
    WordArrayRep after input.layout.outObject (input.layout.length input.layout.outObject) (currentData input input.layout.n) ∧
    IncrementSource.FullCallerFrame before after input.layout.outObject) ∧
  (row input input.layout.n).2≤1 ∧ (∀k< input.layout.n,currentData input input.layout.n (input.layout.outStart+k)<base) ∧
  (magnitude base input.layout.n (fun j=>currentData input input.layout.n (input.layout.outStart+j))+
    (row input input.layout.n).2*base^input.layout.n=
      magnitude base input.layout.n (fun j=>input.old input.layout.outObject (input.layout.outStart+j))+
      magnitude base input.layout.n (aDigit input)) ∧
  ∀k,(k< input.layout.outStart ∨ input.layout.outStart+input.layout.n≤k) → currentData input input.layout.n k=input.old input.layout.outObject k

theorem add_magnitude_total {F : Type} (context : Context F)
    (selected : findFunction context.program "add_magnitude"=some add_magnitude_ast)
    (before : State F) (input : Input) (well : WellScoped before)
    (outRep : WordArrayRep before input.layout.outObject (input.layout.length input.layout.outObject) (input.old input.layout.outObject))
    (aRep : WordArrayRep before input.layout.aObject (input.layout.length input.layout.aObject) (input.old input.layout.aObject)) : Correct context before input:=
  ⟨add_magnitude_call context selected before input well outRep aRep,row_carry input _ (le_refl _),final_normalized input,result_conservation input,currentData_outside input input.layout.n⟩

theorem source_add_magnitude_total (before : State Unit) (input : Input) (well : WellScoped before)
    (outRep : WordArrayRep before input.layout.outObject (input.layout.length input.layout.outObject) (input.old input.layout.outObject))
    (aRep : WordArrayRep before input.layout.aObject (input.layout.length input.layout.aObject) (input.old input.layout.aObject)) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FFTPV.source RH080Next.FFTPV.program ∧ Correct CompareSource.sourceContext before input:=
  ⟨RH080Next.FFTPV.actual_source_syntax,add_magnitude_total _ (by rfl) before input well outRep aRep⟩
theorem fap_source_add_magnitude_total (before : State Unit) (input : Input) (well : WellScoped before)
    (outRep : WordArrayRep before input.layout.outObject (input.layout.length input.layout.outObject) (input.old input.layout.outObject))
    (aRep : WordArrayRep before input.layout.aObject (input.layout.length input.layout.aObject) (input.old input.layout.aObject)) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FapFFTPV.source RH080Next.FapFFTPV.program ∧ Correct CompareSource.fapSourceContext before input:=
  ⟨RH080Next.FapFFTPV.actual_source_syntax,add_magnitude_total _ (by rfl) before input well outRep aRep⟩
theorem recursive_source_add_magnitude_total (before : State Unit) (input : Input) (well : WellScoped before)
    (outRep : WordArrayRep before input.layout.outObject (input.layout.length input.layout.outObject) (input.old input.layout.outObject))
    (aRep : WordArrayRep before input.layout.aObject (input.layout.length input.layout.aObject) (input.old input.layout.aObject)) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧ Correct AddSource.recursiveContext before input:=
  ⟨FFTRecursivePV.actual_source_syntax,add_magnitude_total _ (by rfl) before input well outRep aRep⟩
theorem fap_recursive_source_add_magnitude_total (before : State Unit) (input : Input) (well : WellScoped before)
    (outRep : WordArrayRep before input.layout.outObject (input.layout.length input.layout.outObject) (input.old input.layout.outObject))
    (aRep : WordArrayRep before input.layout.aObject (input.layout.length input.layout.aObject) (input.old input.layout.aObject)) :
    Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧ Correct AddSource.fapRecursiveContext before input:=
  ⟨FapFFTRecursivePV.actual_source_syntax,add_magnitude_total _ (by rfl) before input well outRep aRep⟩

#print axioms add_magnitude_total
#print axioms source_add_magnitude_total
#print axioms fap_source_add_magnitude_total
#print axioms recursive_source_add_magnitude_total
#print axioms fap_recursive_source_add_magnitude_total
end RH080Next.FFTPV.AddMagnitudeSource
