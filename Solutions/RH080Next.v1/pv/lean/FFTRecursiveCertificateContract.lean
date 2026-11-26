/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveTraceAlignment
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open scoped BigOperators

/-- Normalization comes from the actual complete C table-loop invariant. -/
theorem TwiddleSource.View.recursive_normalized {F : Type} {state : State F}
    {tableObject workObject n owner : Nat} {ids : TwiddleSource.Var → Nat}
    {tableData workData : Nat → Nat} {seed : FFT.IntegerModel.CInt}
    (h : TwiddleSource.View state tableObject workObject n ids owner (n/2) tableData workData seed) :
    ∀k,k<n/2 → NormalizedCell tableData k := by
  intro k hk
  constructor
  · simpa only [Nat.mul_comm] using h.tableDigits k hk
  · simpa only [Nat.mul_comm] using h.tableSigns k hk

/-- Domain-index agreement of actual initialized source cells transfers the
independently established kernel input mass, without inspecting C output. -/
theorem input_mass_of_certificate (S : Nat) (input : Nat → Nat) (kernelInput : Nat → FFT.IntegerModel.CInt)
    (inputEq : ∀j,j<2^S → cell input j=kernelInput j)
    (mass : FFT.coefficientMass (2^S) (fun j=>FFT.IntegerModel.decode (kernelInput j))≤362) :
    FFT.coefficientMass (2^S) (fun j=>FFT.IntegerModel.decode (cell input j))≤362 := by
  have equal : FFT.coefficientMass (2^S) (fun j=>FFT.IntegerModel.decode (cell input j))=
      FFT.coefficientMass (2^S) (fun j=>FFT.IntegerModel.decode (kernelInput j)) := by
    unfold FFT.coefficientMass
    apply Finset.sum_congr rfl
    intro j hj
    change ‖FFT.IntegerModel.decode (cell input j)‖=‖FFT.IntegerModel.decode (kernelInput j)‖
    rw [inputEq j (Finset.mem_range.mp hj)]
  rw [equal]
  exact mass

/-- The recursion contract with all numerical primitive-domain premises
supplied by the actual constructed source table and independent kernel data.
Source-table normalization, source input mass and source stage errors are
proved here, rather than left as unchecked main-continuation assumptions. -/
theorem recursive_contract_of_certificate {F G : Type} (context : Context F) (helpers : Helpers context)
    {total S : Nat} (buffers : Buffers total) (input table : Nat → Nat)
    (totalPower : total=2^S) (positive : 0<S) (stageLimit : S≤24)
    (inputNormalized : ∀k,k<total → NormalizedCell input k)
    {tableState : State G} {tableObject workObject owner : Nat} {ids : TwiddleSource.Var → Nat}
    {tableWork : Nat → Nat} {seed : FFT.IntegerModel.CInt}
    (tableView : TwiddleSource.View tableState tableObject workObject (2^S) ids owner ((2^S)/2) table tableWork seed)
    {rest : List FFT.IntegerModel.CInt}
    (twiddles : FFT.IntegerModel.TwiddleTrace seed (FFT.IntegerModel.unit,0) rest)
    (length : ((FFT.IntegerModel.unit,0)::rest).length=(2^S)/2)
    (kernelStages : Nat → List FFT.IntegerModel.CInt) (kernelInput : Nat → FFT.IntegerModel.CInt)
    (chains : ∀t,t<S → FFT.IntegerModel.DecimationTrace (S-(t+1))
      ((FFT.IntegerModel.unit,0)::rest) (kernelStages (t+1)))
    (inputEq : ∀j,j<2^S → cell input j=kernelInput j)
    (mass : FFT.coefficientMass (2^S) (fun j=>FFT.IntegerModel.decode (kernelInput j))≤362)
    (kernelError : ∀t,t<S → ∀j,j<2^t →
      ‖FFT.IntegerModel.decode ((kernelStages (t+1)).getD j (0,0))-FFT.negativeRoot (2*2^t)^j‖≤
        (1/10000000000000000000:ℝ)) :
    StrongContract context buffers input table S 0 0 1 := by
  have entries:=source_table_stage_entries tableView positive twiddles length kernelStages chains
  have tableGood : ∀k,k<total/2 → NormalizedCell table k := by
    rw [totalPower]
    exact TwiddleSource.View.recursive_normalized tableView
  have sourceError : ∀t,t<S → ∀j,j<2^t →
      ‖FFT.IntegerModel.decode ((stages table total (t+1)).getD j (0,0))-FFT.negativeRoot (2*2^t)^j‖≤
        (1/10000000000000000000:ℝ) := by
    intro t ht j hj
    rw [totalPower,entries t ht j hj]
    exact kernelError t ht j hj
  apply recursive_strong_total context helpers buffers input table S totalPower stageLimit inputNormalized tableGood
    (input_mass_of_certificate S input kernelInput inputEq mass) sourceError S 0 0 1 (le_refl _)
  rw [totalPower]
  refine ⟨by positivity,by norm_num,by simp,by norm_num,by simp,?_⟩
  exact Nat.pow_le_pow_right (by norm_num) stageLimit

#print axioms TwiddleSource.View.recursive_normalized
#print axioms input_mass_of_certificate
#print axioms recursive_contract_of_certificate
end RH080Next.FFTPV.RecursiveSource
