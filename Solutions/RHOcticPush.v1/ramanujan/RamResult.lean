import RamBandLow
import RamBandMid
import RamBandHigh
import ActualFinalProfile

/-! Earlier all-real onset and a stronger complete margin profile. Every
literature/RH input is the same as the previous620b theorem; the old stronger
640b-and-above profile is retained exactly. Finite source-C log outputs are
consumed by the three rigorous interval joins, not assumed from native runs. -/
namespace RHOcticPush.Ram
open Real IEANTN Ramanujan640 RHContinuation.Ramanujan RHLimit.Ram620
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def certifiedMargin (x : ℝ) : ℝ :=
  if (640000000000 : ℝ) ≤ x then finalMargin x
  else if (620000000000 : ℝ) ≤ x then 1/400
  else if (619000000000 : ℝ) ≤ x then 3/2000
  else 1/5000

theorem retains_original_margin {x : ℝ} (hx : (640000000000 : ℝ) ≤ x) :
    certifiedMargin x = finalMargin x := by
  simp only [certifiedMargin, if_pos hx]

lemma finalMargin_dominates_source (x : ℝ) : sourceCertifiedMargin x ≤ finalMargin x := by
  have hexp : exp (42:ℝ) ≤ exp 70 := exp_le_exp.mpr (by norm_num)
  by_cases h70 : exp (70:ℝ) ≤ x
  · have h42 : exp (42:ℝ) ≤ x := hexp.trans h70
    simp only [sourceCertifiedMargin,finalMargin,if_pos h42,if_pos h70]
    have hl : 0 < log x := log_pos
      ((one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<70)).trans_le h70)
    have h1 : 0 ≤ (14:ℝ)/log x := by positivity
    have h2 : 0 ≤ (144:ℝ)/(log x)^2 := by positivity
    have ht : (4/5:ℝ) ≤ 1+14/log x+144/(log x)^2 := by linarith
    exact ht.trans (le_max_left _ _)
  · by_cases h42 : exp (42:ℝ) ≤ x
    · simp only [sourceCertifiedMargin,finalMargin,if_pos h42,if_neg h70]
      exact le_max_left _ _
    · simp [sourceCertifiedMargin,finalMargin,h42,h70]

theorem dominates_old_profile {x : ℝ} (hx : (620000000000 : ℝ) ≤ x) :
    RHLimit.Ram620.certifiedMargin620 x ≤ certifiedMargin x := by
  by_cases h640 : (640000000000 : ℝ) ≤ x
  · simpa [certifiedMargin, RHLimit.Ram620.certifiedMargin620, h640] using finalMargin_dominates_source x
  · norm_num [certifiedMargin, RHLimit.Ram620.certifiedMargin620, h640, hx]

theorem actual_ramanujan_profile (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (617500000000 : ℝ) ≤ x) : certifiedMargin x ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  unfold certifiedMargin
  split_ifs with h640 h620 h619
  · exact final_ramanujan_profile hRH hT2 hJ hL hU hS h640
  · have h := bridge_high hRH hGM hP hJ hT1 hL hU (z := log x)
      (by simpa only [exp_log hx0] using h620)
      (by rw [exp_log hx0]; linarith)
    simpa only [exp_log hx0] using h
  · have h := bridge_mid hRH hGM hP hJ hT1 hL hU (z := log x)
      (by simpa only [exp_log hx0] using h619)
      (by rw [exp_log hx0]; linarith)
    simpa only [exp_log hx0] using h
  · have h := bridge_low hRH hGM hP hJ hT1 hL hU (z := log x)
      (by simpa only [exp_log hx0] using hx)
      (by rw [exp_log hx0]; linarith)
    simpa only [exp_log hx0] using h

theorem actual_prime_counting_gap (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (617500000000 : ℝ) ≤ x) :
    certifiedMargin x*x^2/(log x)^6 ≤
      exp 1*x/log x*primeCounting (x/exp 1)-(primeCounting x)^2 := by
  have hr := actual_ramanujan_profile hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*(certifiedMargin x*x^2/(log x)^6)=certifiedMargin x := by
    field_simp [hx0.ne',hl.ne']
  change certifiedMargin x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

theorem actual_ramanujan_strict (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (617500000000 : ℝ) ≤ x) :
    (primeCounting x)^2 < exp 1*x/log x*primeCounting (x/exp 1) := by
  have h := actual_prime_counting_gap hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hm : 0 < certifiedMargin x := by
    unfold certifiedMargin finalMargin
    split_ifs <;> positivity
  have hp : 0 < certifiedMargin x*x^2/(log x)^6 := by positivity
  linarith

#print axioms actual_ramanujan_profile
#print axioms actual_prime_counting_gap
#print axioms actual_ramanujan_strict
#print axioms retains_original_margin
#print axioms dominates_old_profile
end RHOcticPush.Ram
