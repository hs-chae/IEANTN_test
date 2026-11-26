/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootTermStep
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

def updatedTerms (n j : Nat) : Region → Int:=
  Function.update (Function.update (regionValue n j) .ct (nextCosineTerm n j)) .st (nextSineTerm n j)

/-- All six source instructions computing the next cosine and sine terms.
The original grid-specific kernel guard bounds are consumed by both complete
multiply/copy/divide paths and every named stored value is transported. -/
theorem paired_terms_execution {F : Type} (context : Context F) (functions : Functions context)
    {before : State F} {input : Input} {owner statusId indexId j : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data (j+1))
    (tracked : Tracked input data (regionValue input.n j)) (grid : OriginalGrid input.n) (hj : j<10) :
    ∃after nextData,ExecList context before (termStatements 12 cosineDivisor++termStatements 18 sineDivisor) .normal after ∧
      EveryList context before (termStatements 12 cosineDivisor++termStatements 18 sineDivisor) .normal after ∧
      Runtime after input owner statusId indexId ids nextData (j+1) ∧ Tracked input nextData (updatedTerms input.n j) ∧
      IncrementSource.FullCallerFrame before after input.layout.object ∧
      ∀k,k < input.layout.size → (k < input.layout.workStart ∨ input.layout.workStart+80≤ k) → nextData k=data k := by
  obtain ⟨cosNonnegative,cosSmall,sinNonnegative,sinSmall,ctSmall,stSmall,x2Small,crSmall,srSmall⟩:=original_intermediate_bounds input.n j grid hj
  obtain ⟨cosPositive,cosBound,sinPositive,sinBound⟩:=iteration_divisors j hj
  obtain ⟨middle,data1,cosRun,cosEvery,cosRuntime,cosTracked,cosFrame,cosOutside⟩:=term_execution context functions h (regionValue input.n j) tracked
    .ct 12 (by omega) rfl cosineDivisor (2*(j+1)*(2*(j+1)-1)) cosPositive cosBound cosine_divisor_pure
    (fun rt=>cosine_divisor_eval context rt hj) ctSmall x2Small cosNonnegative
  have cosineValues : Function.update (regionValue input.n j) .ct
      (((regionValue input.n j .ct*regionValue input.n j .x2)/FFT.IntegerModel.unit)/((2*(j+1)*(2*(j+1)-1):Nat):Int))=
      Function.update (regionValue input.n j) .ct (nextCosineTerm input.n j):=rfl
  rw [cosineValues] at cosTracked
  obtain ⟨after,nextData,sinRun,sinEvery,sinRuntime,sinTracked,sinFrame,sinOutside⟩:=term_execution context functions cosRuntime
    (Function.update (regionValue input.n j) .ct (nextCosineTerm input.n j)) cosTracked .st 18 (by omega) rfl
    sineDivisor (2*(j+1)*(2*(j+1)+1)) sinPositive sinBound sine_divisor_pure
    (fun rt=>sine_divisor_eval context rt hj) stSmall x2Small sinNonnegative
  refine ⟨after,nextData,append_normal cosRun sinRun,every_append cosEvery sinEvery,sinRuntime,sinTracked,full_caller_trans cosFrame sinFrame,?_⟩
  intro k hk outside
  exact (sinOutside k hk outside).trans (cosOutside k hk outside)

#print axioms paired_terms_execution
end RH080Next.FFTPV.RootSource
