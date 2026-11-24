import SpectralRam606Cells
import IEANTN.Nodes.RHPrimeCounting.v5.Conclusions

/-! A genuine new typed network edge: actual compensation profile to a local
Ramanujan gap. No source theorem, RH or desired Ramanujan conclusion is hidden
in the consumer. Its compensation input is supplied by the separate signed
Perron/Nicolas proof. Frozen original and earlier synthesis sources are retained.
-/
namespace RHOcticPush.SpectralRam
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram RHOcticPush.Correlated
open RHOcticPush.Spectral076 RHOcticPush.BoxPerron
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem actual_pair_of_profile (hE : RHPrimeCounting.v5.compensation_profile)
    {k z : ℝ} (hk : 0 ≤ k) (hz : 25 ≤ z) :
    k * GM.error (exp z) - exp 1 * GM.error (exp (z - 1)) ≤ budget k z := by
  have hx := hE (exp z) (Real.exp_le_exp.mpr (by linarith : (24 : ℝ) ≤ z))
  have hy := hE (exp (z - 1)) (Real.exp_le_exp.mpr (by linarith : (24 : ℝ) ≤ z - 1))
  change |GM.error (exp z)| ≤ Spectral076.profile (log (exp z)) at hx
  change |GM.error (exp (z - 1))| ≤ Spectral076.profile (log (exp (z - 1))) at hy
  simp only [Real.log_exp] at hx hy
  have hxu := (le_abs_self (GM.error (exp z))).trans hx
  have hyl := (neg_le_abs (GM.error (exp (z - 1)))).trans hy
  have h1 := mul_le_mul_of_nonneg_left hxu hk
  have h2 := mul_le_mul_of_nonneg_left hyl (Real.exp_pos 1).le
  unfold budget
  linarith

theorem actual_margin_from_profile (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {l u z k a b : ℝ} (hl : 27 ≤ l) (hu : u ≤ 42) (hlz : l ≤ z) (hzu : z ≤ u)
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000)
    (hk0 : 0 ≤ k) (hkw : k ≤ 2 * pN 20 u)
    (ha : a ≤ -88 / 100 + lowerPowers l u)
    (hb : 68 / 100 + upperPowers (l - 1) ≤ b) : margin k a b z ≤ RamStudy.RG (exp z) := by
  have hz27 : (27 : ℝ) ≤ z := hl.trans hlz
  have hz0 : 0 < z := by linarith
  have hzm1 : 0 < z - 1 := by linarith
  have hz42 : z ≤ 42 := hzu.trans hu
  have hz2 : 2 ≤ exp z := exp_one_gt_two.le.trans (exp_le_exp.mpr (by linarith))
  have hc0 := (source_deficit_pos hU hz0 hz2 hz42).le
  have hcq := source_deficit_upper hL hz0 hz2 hz42
  have hsq := pow_le_pow_left₀ hc0 hcq 2
  have hF : 0 ≤ F z := by unfold F; positivity
  have hH : 0 ≤ H z := by unfold H; positivity
  have hQ : 0 ≤ Q z := by unfold Q; positivity
  have hT : 0 ≤ T z := by unfold T; positivity
  have hbase := SharpBase.actual_sharp_base hz27
  have hactual := actual_signed_gap (by linarith : 1 < z) hbase
    (le_refl (deficit z)) (le_refl (deficit (z - 1)))
  have hactual' : SharpBase.sharpBase z - H z * deficit (z - 1) +
      2 * RamStudy.w z * F z * deficit z - (deficit z)^2 * Q z ≤
      RamStudy.RG (exp z) := by
    convert hactual using 1 <;> unfold F H Q <;> ring
  have hw : pN 20 u ≤ RamStudy.w z :=
    (pN_antitone hz0 hzu 20).trans (by
      simpa only [actual_w_eq] using
        (actual_factorial_barrier26 (by linarith : 26 ≤ z)).1)
  have hkactual : k ≤ 2 * RamStudy.w z := by linarith
  have hkwc := mul_le_mul_of_nonneg_right hkactual (mul_nonneg hF hc0)
  have hsqQ := mul_le_mul_of_nonneg_right hsq hQ
  have ht := table1_bridge480 hTab hcut hcap
  have hpow := powers_lower hL (by linarith : 26 ≤ l) hlz hzu hu
  have hpow' := powers_upper hU (by linarith : 26 ≤ l - 1)
    (by linarith : l - 1 ≤ z - 1) (by linarith : z - 1 ≤ 42)
  have ha' : a ≤ psiDeficit z + primePart z := by linarith
  have hb' : psiDeficit (z - 1) + primePart (z - 1) ≤ b := by linarith
  have hpa := mul_le_mul_of_nonneg_left ha' (mul_nonneg hk0 hF)
  have hpb := mul_le_mul_of_nonneg_left hb' hH
  have hpair := actual_pair_of_profile hE hk0 (by linarith : 25 ≤ z)
  have hpt := mul_le_mul_of_nonneg_left hpair hT
  have hidentity := linear_identity (k := k) hz0.ne' (by linarith : z ≠ 1)
  unfold margin
  nlinarith only [hactual', hkwc, hsqQ, hpa, hpb, hpt, hidentity]


theorem profile_gap_0 (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (28448019/1048576 : ℝ) ≤ z) (hu : z ≤ (113793801/4194304 : ℝ))
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (5199/2500 : ℝ) ≤ 2 * pN 20 (113793801/4194304 : ℝ) := by
    norm_num [pN, Finset.sum_range_succ, Nat.factorial]
  have ha := lower_0.trans (by
    linarith [lowerNoMax_le (28448019/1048576 : ℝ) (113793801/4194304 : ℝ)] :
      -88 / 100 + lowerNoMax (28448019/1048576 : ℝ) (113793801/4194304 : ℝ) ≤ -88 / 100 + lowerPowers (28448019/1048576 : ℝ) (113793801/4194304 : ℝ))
  have h := actual_margin_from_profile hE hTab hL hU
    (by norm_num : 27 ≤ (28448019/1048576 : ℝ)) (by norm_num : (113793801/4194304 : ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (5199/2500 : ℝ)) hk ha upper_0
  have hn := numeric_0 z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

theorem profile_gap_1 (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (113793801/4194304 : ℝ) ≤ z) (hu : z ≤ (56897763/2097152 : ℝ))
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (5199/2500 : ℝ) ≤ 2 * pN 20 (56897763/2097152 : ℝ) := by
    norm_num [pN, Finset.sum_range_succ, Nat.factorial]
  have ha := lower_1.trans (by
    linarith [lowerNoMax_le (113793801/4194304 : ℝ) (56897763/2097152 : ℝ)] :
      -88 / 100 + lowerNoMax (113793801/4194304 : ℝ) (56897763/2097152 : ℝ) ≤ -88 / 100 + lowerPowers (113793801/4194304 : ℝ) (56897763/2097152 : ℝ))
  have h := actual_margin_from_profile hE hTab hL hU
    (by norm_num : 27 ≤ (113793801/4194304 : ℝ)) (by norm_num : (56897763/2097152 : ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (5199/2500 : ℝ)) hk ha upper_1
  have hn := numeric_1 z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

theorem profile_gap_2 (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (56897763/2097152 : ℝ) ≤ z) (hu : z ≤ (1778109/65536 : ℝ))
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (5199/2500 : ℝ) ≤ 2 * pN 20 (1778109/65536 : ℝ) := by
    norm_num [pN, Finset.sum_range_succ, Nat.factorial]
  have ha := lower_2.trans (by
    linarith [lowerNoMax_le (56897763/2097152 : ℝ) (1778109/65536 : ℝ)] :
      -88 / 100 + lowerNoMax (56897763/2097152 : ℝ) (1778109/65536 : ℝ) ≤ -88 / 100 + lowerPowers (56897763/2097152 : ℝ) (1778109/65536 : ℝ))
  have h := actual_margin_from_profile hE hTab hL hU
    (by norm_num : 27 ≤ (56897763/2097152 : ℝ)) (by norm_num : (1778109/65536 : ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (5199/2500 : ℝ)) hk ha upper_2
  have hn := numeric_2 z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

theorem profile_gap_3 (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1778109/65536 : ℝ) ≤ z) (hu : z ≤ (28451469/1048576 : ℝ))
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (5199/2500 : ℝ) ≤ 2 * pN 20 (28451469/1048576 : ℝ) := by
    norm_num [pN, Finset.sum_range_succ, Nat.factorial]
  have ha := lower_3.trans (by
    linarith [lowerNoMax_le (1778109/65536 : ℝ) (28451469/1048576 : ℝ)] :
      -88 / 100 + lowerNoMax (1778109/65536 : ℝ) (28451469/1048576 : ℝ) ≤ -88 / 100 + lowerPowers (1778109/65536 : ℝ) (28451469/1048576 : ℝ))
  have h := actual_margin_from_profile hE hTab hL hU
    (by norm_num : 27 ≤ (1778109/65536 : ℝ)) (by norm_num : (28451469/1048576 : ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (5199/2500 : ℝ)) hk ha upper_3
  have hn := numeric_3 z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

theorem profile_gap_4 (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (28451469/1048576 : ℝ) ≤ z) (hu : z ≤ (28454919/1048576 : ℝ))
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (5199/2500 : ℝ) ≤ 2 * pN 20 (28454919/1048576 : ℝ) := by
    norm_num [pN, Finset.sum_range_succ, Nat.factorial]
  have ha := lower_4.trans (by
    linarith [lowerNoMax_le (28451469/1048576 : ℝ) (28454919/1048576 : ℝ)] :
      -88 / 100 + lowerNoMax (28451469/1048576 : ℝ) (28454919/1048576 : ℝ) ≤ -88 / 100 + lowerPowers (28451469/1048576 : ℝ) (28454919/1048576 : ℝ))
  have h := actual_margin_from_profile hE hTab hL hU
    (by norm_num : 27 ≤ (28451469/1048576 : ℝ)) (by norm_num : (28454919/1048576 : ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (5199/2500 : ℝ)) hk ha upper_4
  have hn := numeric_4 z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

theorem bridge606_from_profile (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (606000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 610000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (28448019/1048576 : ℝ) ≤ (606000000000 : ℝ) := by
    interval_decide 80 (trust := kernel)
  have hup : (610000000000 : ℝ) ≤ exp (28454919/1048576 : ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : (28448019/1048576 : ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (28454919/1048576 : ℝ) := exp_le_exp.mp (hcap.trans hup)
  have hc : (480000000000 : ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000 : ℝ) := by linarith
  by_cases h0 : z ≤ (113793801/4194304 : ℝ)
  · exact profile_gap_0 hE hTab hL hU (by linarith) h0 hc hp
  by_cases h1 : z ≤ (56897763/2097152 : ℝ)
  · exact profile_gap_1 hE hTab hL hU (by linarith) h1 hc hp
  by_cases h2 : z ≤ (1778109/65536 : ℝ)
  · exact profile_gap_2 hE hTab hL hU (by linarith) h2 hc hp
  by_cases h3 : z ≤ (28451469/1048576 : ℝ)
  · exact profile_gap_3 hE hTab hL hU (by linarith) h3 hc hp
  exact profile_gap_4 hE hTab hL hU (by linarith) hu hc hp

theorem local_actual_gap (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {x : ℝ} (hx : (606000000000 : ℝ) ≤ x) (hu : x ≤ (610000000000 : ℝ)) :
    (1 / 1000 : ℝ) * x^2 / (log x)^6 ≤ RamanujanGap.v1.gap x := by
  have hx0 : 0 < x := by linarith
  have hr := bridge606_from_profile hE hTab hL hU (z := log x)
    (by simpa only [exp_log hx0] using hx) (by simpa only [exp_log hx0] using hu)
  rw [exp_log hx0] at hr
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6 / x^2 := by positivity
  have he : (log x^6 / x^2) * ((1 / 1000 : ℝ) * x^2 / (log x)^6) = 1 / 1000 := by
    field_simp [hx0.ne', hl.ne']
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

#print axioms actual_pair_of_profile
#print axioms actual_margin_from_profile
#print axioms profile_gap_0
#print axioms profile_gap_1
#print axioms profile_gap_2
#print axioms profile_gap_3
#print axioms profile_gap_4
#print axioms bridge606_from_profile
#print axioms local_actual_gap
end RHOcticPush.SpectralRam
