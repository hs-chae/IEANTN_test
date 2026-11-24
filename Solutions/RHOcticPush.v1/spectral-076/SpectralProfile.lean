import RemainderScalar

/-! The full signed-transfer function and two conservative scalar corollaries.
These are scalar proofs only; the actual arithmetic consumer is assembled
separately from the complete zero and general-source transport proofs. -/
namespace RHOcticPush.Spectral076
open Real Set
set_option maxHeartbeats 0

noncomputable def profile (L : ℝ) : ℝ :=
  (579/125 : ℝ)+(47/1000)*(1+4/(L-8))*(Real.exp (L/2)/L^2)

theorem profile_lt_076 {L : ℝ} (hL : 24 ≤ L) :
    profile L < (76/1000)*(Real.exp (L/2)/L^2) := by
  have h := spectral_scalar_budget_eight hL
  unfold profile
  linarith

lemma exp_square_ratio_lower35 {L : ℝ} (hL : 35 ≤ L) :
    (10000 : ℝ) < Real.exp (L/2)/L^2 := by
  have hm := RHOcticPush.GM.ratio_mono
    (show (35 : ℝ) ∈ Ici 24 by norm_num)
    (show L ∈ Ici 24 from (show (24 : ℝ) ≤ L by linarith)) hL
  have h0 : 0 < L := by linarith
  have ha : (10000 : ℝ) < Real.exp (35/2)/35^2 := by
    interval_decide 80 (trust := kernel) <;> ring
  have hh := mul_le_mul hL hm (by positivity : 0 ≤ Real.exp (35/2)/35^3) h0.le
  have he : L*(Real.exp (L/2)/L^3) = Real.exp (L/2)/L^2 := by field_simp <;> ring
  rw [he] at hh
  linarith

/-- A separate stronger all-real scalar consequence, using the same actual
signed-transfer function and no new mathematical or numerical premise. -/
theorem profile_lt_055 {L : ℝ} (hL : 35 ≤ L) :
    profile L < (55/1000)*(Real.exp (L/2)/L^2) := by
  have hd : 0 < L-8 := by linarith
  have hf : 4/(L-8) ≤ (4/27 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hE := exp_square_ratio_lower35 hL
  have hE0 : 0 ≤ Real.exp (L/2)/L^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (show (47/1000 : ℝ)*(1+4/(L-8)) ≤ (47/1000)*(31/27) by linarith) hE0
  unfold profile
  linarith

#print axioms profile_lt_076
#print axioms profile_lt_055
end RHOcticPush.Spectral076
