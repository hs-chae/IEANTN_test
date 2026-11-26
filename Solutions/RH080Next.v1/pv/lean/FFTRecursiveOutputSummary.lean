/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveCertificateRun
import FFTOutputSumBase
import FFTCertificateComposition
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect WordArrays
open scoped BigOperators

theorem real_component_small (z : FFT.IntegerModel.CInt) (bound : ‖FFT.IntegerModel.decode z‖≤400) :
    z.1.natAbs≤400*10^36 := by
  have unitPos : (0:ℝ)<FFT.IntegerModel.unit := by norm_num [FFT.IntegerModel.unit]
  have re:=(Complex.abs_re_le_norm (FFT.IntegerModel.decode z)).trans bound
  change |(z.1:ℝ)/(FFT.IntegerModel.unit:ℝ)|≤400 at re
  rw [abs_div,abs_of_pos unitPos] at re
  have integerBound : |(z.1:ℝ)|≤(400*10^36:Nat) := by
    have bound:=(div_le_iff₀ unitPos).mp re
    norm_num [FFT.IntegerModel.unit] at bound ⊢
    exact bound
  have castBound : |z.1|≤(400*10^36:Nat) := by exact_mod_cast integerBound
  rw [Int.abs_eq_natAbs] at castBound
  exact_mod_cast castBound

/-- The source sum-loop's pointwise numeric fields follow from the actual
recursive Call, output normalization, certificate identity and true norm bound. -/
theorem CallPost.output_sum_fields {F : Type} {total : Nat} {buffers : Buffers total}
    {S : Nat} {input table oldOutput oldWork output work : Nat → Nat} {before after : State F}
    (post : CallPost buffers S 0 0 1 input table oldOutput oldWork before after output work)
    {kernelOutput : List FFT.IntegerModel.CInt} (outputEq : cells output 0 (2^S)=kernelOutput)
    (normBound : ∀k,k<2^S → ‖FFT.IntegerModel.decode (kernelOutput.getD k (0,0))‖≤400) :
    (∀k,k<2^S → ∀d,d<5 → output (k*12+d)<1000000000) ∧
    (∀k,k<2^S → (ComplexSource.pair output (k*12)).1=(kernelOutput.getD k (0,0)).1) ∧
    (∀k,k<2^S → (kernelOutput.getD k (0,0)).1.natAbs≤400*10^36) := by
  have entries : ∀k,k<2^S → cell output k=kernelOutput.getD k (0,0) := by
    intro k hk
    have same:=congrArg (fun xs : List FFT.IntegerModel.CInt=>xs.getD k (0,0)) outputEq
    simpa only [cells_getD _ _ _ _ hk,Nat.zero_add] using same
  refine ⟨?_,?_,?_⟩
  · intro k hk d hd
    simpa only [Fin.val_zero,Nat.zero_add,Nat.mul_comm,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] using
      (post.normalized k hk).1 (0:Fin 2) d hd
  · intro k hk
    have same:=congrArg Prod.fst (entries k hk)
    simpa only [cell,ComplexSource.pair,Nat.mul_comm] using same
  · intro k hk;exact real_component_small _ (normBound k hk)

/-- Convert finite indexing to the same list absolute-sum used by the kernel
certificate, by structural list induction rather than evaluating its elements. -/
theorem partialSum_getD (xs : List FFT.IntegerModel.CInt) :
    OutputSumSource.partialSum (fun k=>xs.getD k (0,0)) xs.length=FFT.IntegerModel.absSum xs := by
  induction xs with
  | nil => simp [OutputSumSource.partialSum,FFT.IntegerModel.absSum]
  | cons x xs ih =>
    simp [OutputSumSource.partialSum,FFT.IntegerModel.absSum,Finset.sum_range_succ'] at ih ⊢
    omega

theorem CallPost.output_partialSum_eq {F : Type} {total : Nat} {buffers : Buffers total}
    {S : Nat} {input table oldOutput oldWork output work : Nat → Nat} {before after : State F}
    (post : CallPost buffers S 0 0 1 input table oldOutput oldWork before after output work)
    {kernelOutput : List FFT.IntegerModel.CInt} (outputEq : cells output 0 (2^S)=kernelOutput) :
    OutputSumSource.partialSum (fun k=>cell output k) (2^S)=FFT.IntegerModel.absSum kernelOutput := by
  have length : kernelOutput.length=2^S := by rw [←outputEq];exact cells_length _ _ _
  have sumEq : OutputSumSource.partialSum (fun k=>cell output k) (2^S)=
      OutputSumSource.partialSum (fun k=>kernelOutput.getD k (0,0)) (2^S) := by
    unfold OutputSumSource.partialSum
    apply Finset.sum_congr rfl
    intro k hk
    have inside:=Finset.mem_range.mp hk
    have same:=congrArg (fun xs : List FFT.IntegerModel.CInt=>xs.getD k (0,0)) outputEq
    simp only [cells_getD _ _ _ _ inside,Nat.zero_add] at same
    exact congrArg (fun z : FFT.IntegerModel.CInt=>z.1.natAbs) same
  rw [sumEq,←length]
  exact partialSum_getD kernelOutput

/-- An existing accepted exact certificate sum receipt transfers to the real
source output sum, with no expansion of the huge literal output list. -/
theorem CallPost.output_partialSum_receipt {F : Type} {total : Nat} {buffers : Buffers total}
    {S : Nat} {input table oldOutput oldWork output work : Nat → Nat} {before after : State F}
    (post : CallPost buffers S 0 0 1 input table oldOutput oldWork before after output work)
    {kernelOutput : List FFT.IntegerModel.CInt} (outputEq : cells output 0 (2^S)=kernelOutput)
    (totalAbs : Nat) (receipt : FFT.IntegerModel.absSum kernelOutput=totalAbs) :
    OutputSumSource.partialSum (fun k=>cell output k) (2^S)=totalAbs :=
  (post.output_partialSum_eq outputEq).trans receipt

#print axioms CallPost.output_sum_fields
#print axioms partialSum_getD
#print axioms CallPost.output_partialSum_receipt
end RH080Next.FFTPV.RecursiveSource
