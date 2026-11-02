/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Table4.Program

namespace FKS2Table4
open FKS2Scalar SumStability

def suffixError : ℚ := 1/10^30
def sumUpper : ℚ := qsum/(1-gamma 29)
def totalForwardError : ℚ := scale*(sumUpper-qsum)+suffixError

def scaledOutput : ℚ := (round64 (qsum*scale)).getD 0
def anchorOutput : ℚ := (round64 (scaledOutput+anchorUpper)).getD 0
def pointOutput : ℚ := (round64 (anchorOutput+pointUpper)).getD 0

theorem suffix_checks :
    scaledOutput=scale*qsum ∧
    round64 (scaledOutput+anchorUpper)=some anchorOutput ∧
    round64 (anchorOutput+pointUpper)=some pointOutput ∧
    round64 (pointOutput+tailUpper)=some q ∧
    additionCheck (scaledOutput+anchorUpper) anchorOutput=true ∧
    additionCheck (anchorOutput+pointUpper) pointOutput=true ∧
    additionCheck (pointOutput+tailUpper) q=true ∧
    |anchorOutput-(scaledOutput+anchorUpper)| ≤ 1/10^31 ∧
    |pointOutput-(anchorOutput+pointUpper)| ≤ 1/10^31 ∧
    |q-(pointOutput+tailUpper)| ≤ 1/10^31 := by native_decide

theorem suffix_roundoff :
    |q-(scale*qsum+anchorUpper+pointUpper+tailUpper)| ≤ suffixError := by
  have h1 := (abs_le.mp suffix_checks.2.2.2.2.2.2.2.1)
  have h2 := (abs_le.mp suffix_checks.2.2.2.2.2.2.2.2.1)
  have h3 := (abs_le.mp suffix_checks.2.2.2.2.2.2.2.2.2)
  rw [suffix_checks.1] at h1
  rw [abs_le]
  unfold suffixError
  constructor <;> linarith

theorem budget_checks :
    0 ≤ gamma 29 ∧ gamma 29 < 1 ∧ 0 ≤ scale ∧ 0 ≤ qsum ∧
    (inputValues.map abs).sum = inputValues.sum ∧ 0 ≤ inputValues.sum ∧
    |q-(scale*qsum+anchorUpper+pointUpper+tailUpper)| ≤ suffixError ∧
    0 ≤ totalForwardError ∧ totalForwardError ≤ 1/10^29 ∧
    q+totalForwardError < (5:ℚ)/10^16 := by native_decide

theorem sum_upper : (inputValues.sum:ℚ) ≤ (sumUpper:ℝ) := by
  have h := kernel_stability
  have he := budget_checks.2.2.2.2.1
  rw [he] at h
  have hγ : (gamma 29:ℝ)<1 := by exact_mod_cast budget_checks.2.1
  have hl := (abs_le.mp h).1
  unfold sumUpper
  simp only [Rat.cast_div,Rat.cast_sub,Rat.cast_one]
  apply (le_div_iff₀ (by linarith : (0:ℝ)<1-(gamma 29:ℝ))).mpr
  nlinarith

/-- The total budget uses the general source-linked stability theorem, not an independent
exact-target comparison. Input enclosures are upward; they are consumed in this inequality. -/
theorem verified_output_allowance : allowance ≤ (q:ℝ)+(totalForwardError:ℝ) := by
  have hc := scaled_cells_upper
  have hs := mul_le_mul_of_nonneg_left sum_upper
    (show (0:ℝ)≤(scale:ℝ) by exact_mod_cast budget_checks.2.2.1)
  have hpost : |(q:ℝ)-((scale:ℝ)*(qsum:ℝ)+(anchorUpper:ℝ)+
      (pointUpper:ℝ)+(tailUpper:ℝ))| ≤ (suffixError:ℝ) := by
    exact_mod_cast suffix_roundoff
  have h := (abs_le.mp hpost).1
  unfold allowance totalForwardError
  push_cast
  linarith [anchor_upper,point_upper,tail_upper,hc,hs]

/-- Arbitrary-output contract of this actual source/array configuration. -/
theorem verified_fks2_transport {out : ℚ} (h : ExecTransport selected out) :
    allowance ≤ (out:ℝ)+(totalForwardError:ℝ) := by
  rw [output_unique h]
  exact verified_output_allowance

theorem selected_execution_witness : ∃ out : ℚ,
    ExecTransport selected out ∧ allowance ≤ (out:ℝ)+(totalForwardError:ℝ) :=
  ⟨q,concrete_execution,verified_fks2_transport concrete_execution⟩

theorem certified_allowance : allowance < (5:ℝ)/10^16 := by
  have hnum : (q:ℝ)+(totalForwardError:ℝ)<(5:ℝ)/10^16 := by
    have h := (Rat.cast_lt (K := ℝ)).2 budget_checks.2.2.2.2.2.2.2.2.2
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using h
  exact (verified_fks2_transport concrete_execution).trans_lt hnum

theorem numerical_pi (hpsi : QRHCH2.v5.psi_refined_bound)
    (hOld : IEANTN.Eπ (Real.exp 300) ≤ 1.6997e-12) :
    IEANTN.HasNumericalBound IEANTN.Eπ ((5:ℝ)/10^16) (Real.exp 330) := by
  intro x hx
  exact (whole_ray_transport (theta_input hpsi) hOld x hx).trans certified_allowance.le

end FKS2Table4
