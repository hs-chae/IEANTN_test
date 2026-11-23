import Ram620Leaves
namespace RHLimit.Ram620
open Real IEANTN Ramanujan640 RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def certifiedMargin620 (x : ℝ) : ℝ :=
  if (640000000000:ℝ) ≤ x then sourceCertifiedMargin x else 1/1000

lemma retains_original_margin {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    certifiedMargin620 x = sourceCertifiedMargin x := by
  simp only [certifiedMargin620,if_pos hx]

lemma onset_ratio : (620000000000:ℚ)/640000000000 = 31/32 := by norm_num

theorem actual_ramanujan_620b_profile (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (620000000000:ℝ) ≤ x) : certifiedMargin620 x ≤ RamStudy.RG x := by
  unfold certifiedMargin620
  split_ifs with h640
  · exact source_ramanujan_profile hRH hT2 hJ hL hU hS h640
  · exact actual_ramanujan_620b hRH hGM hP hJ hT1 hT2 hL hU hS hx

theorem actual_prime_counting_gap620 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (620000000000:ℝ) ≤ x) :
    certifiedMargin620 x*x^2/(log x)^6 ≤
      exp 1*x/log x*primeCounting (x/exp 1)-(primeCounting x)^2 := by
  have hr := actual_ramanujan_620b_profile hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*(certifiedMargin620 x*x^2/(log x)^6)=certifiedMargin620 x := by
    field_simp [hx0.ne',hl.ne']
  change certifiedMargin620 x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr


theorem actual_ramanujan_strict620 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (620000000000:ℝ) ≤ x) :
    (primeCounting x)^2 < exp 1*x/log x*primeCounting (x/exp 1) := by
  have h := actual_prime_counting_gap620 hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hm : 0 < certifiedMargin620 x := by
    unfold certifiedMargin620 sourceCertifiedMargin
    split_ifs <;> norm_num
  have hp : 0 < certifiedMargin620 x*x^2/(log x)^6 := by positivity
  linarith
#print axioms actual_ramanujan_strict620
#print axioms retains_original_margin
#print axioms actual_ramanujan_620b_profile
#print axioms actual_prime_counting_gap620
end RHLimit.Ram620
