import OcticDerivativeMoments

/-! Complete absolute Fourier moments and the small-ordinate logarithmic hole.
Numerical upper bounds on M0 and M1 are deliberately separate obligations. -/
namespace RHOcticPush.FourierMoments
open Real Set MeasureTheory
open RHOcticPush.DerivativeBounds RHOcticPush.DerivativeMoments
open RHOcticPush.BPTSpecialization
set_option maxHeartbeats 0

noncomputable def F (y : ℝ) := |EvenKernel.transform 4 y|
noncomputable def M0 := ∫ y in Ioi (0 : ℝ), F y
noncomputable def M1 := ∫ y in Ioi (0 : ℝ), F y * log y

lemma F_continuous : Continuous F :=
  (continuous_iff_continuousAt.mpr
    (fun y => (transform_hasDerivAt y).continuousAt)).abs

lemma F_nonneg (y : ℝ) : 0 ≤ F y := abs_nonneg _
lemma F_mass (y : ℝ) : F y ≤ 16 / 9 := by
  have h := RHOcticPush.Decay.transform_abs_le_mass 4 y
  norm_num [EvenKernel.mass] at h
  exact h

lemma F_integrable : IntegrableOn F (Ioi 0) := by
  have ht : IntegrableOn F (Ioi 1) := by
    apply ((inv_sq_integrable (by norm_num : (0 : ℝ) < 1)).const_mul 32).mono'
      F_continuous.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (F_nonneg y)]
    simpa [F, div_eq_mul_inv] using RHOcticPush.Decay.transform_abs_le_decay
      (show y ≠ 0 by linarith [hy.out])
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1), integrableOn_union]
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
    (F_continuous.intervalIntegrable 0 1), ht⟩

lemma F_log_integrable : IntegrableOn (fun y => F y * log y) (Ioi 0) := by
  have ht : IntegrableOn (fun y => F y * log y) (Ioi 1) := by
    apply integrable_abs_mul_log_of_decay (by norm_num)
      (f := EvenKernel.transform 4)
      (continuous_iff_continuousAt.mpr
        (fun y => (transform_hasDerivAt y).continuousAt)).continuousOn
    intro y hy
    exact RHOcticPush.Decay.transform_abs_le_decay (by linarith [hy.out])
  have hs : IntervalIntegrable (fun y => F y * log y) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul F_continuous.continuousOn
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1), integrableOn_union]
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hs, ht⟩

lemma log_ratio_integrable {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    IntegrableOn (fun y : ℝ => log (y / q)) (Ioc 0 c) := by
  have hs : IntegrableOn (fun y : ℝ => log y - log q) (Ioc 0 c) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le).mp
      (intervalIntegral.intervalIntegrable_log'.sub intervalIntegrable_const)
  apply hs.congr_fun _ measurableSet_Ioc
  intro y hy
  exact (Real.log_div (ne_of_gt hy.1) hq.ne').symm

lemma log_ratio_self_integral {c : ℝ} (hc : 0 < c) :
    (∫ y in Ioc (0 : ℝ) c, log (y / c)) = -c := by
  have he : (∫ y in Ioc (0 : ℝ) c, log (y / c)) =
      ∫ y in Ioc (0 : ℝ) c, log y - log c := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    exact Real.log_div (ne_of_gt hy.1) hc.ne'
  rw [he, ← intervalIntegral.integral_of_le hc.le,
    intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_log' intervalIntegrable_const,
    integral_log, intervalIntegral.integral_const]
  simp

lemma weighted_ratio_integrable {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun y => F y * log (y / q)) (Ioi 0) := by
  have hs := F_log_integrable.sub (F_integrable.mul_const (log q))
  apply hs.congr_fun _ measurableSet_Ioi
  intro y hy
  change F y * log y - F y * log q = F y * log (y / q)
  rw [Real.log_div (ne_of_gt hy) hq.ne']
  ring

lemma full_ratio_integral {q : ℝ} (hq : 0 < q) :
    (∫ y in Ioi (0 : ℝ), F y * log (y / q)) =
      M0 * log (1 / q) + M1 := by
  calc
    _ = ∫ y in Ioi (0 : ℝ), F y * log y - F y * log q := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [Real.log_div (ne_of_gt hy) hq.ne']
      ring
    _ = M0 * log (1 / q) + M1 := by
      rw [integral_sub F_log_integrable (F_integrable.mul_const (log q)), integral_mul_const]
      unfold M0 M1
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hq.ne', Real.log_one]
      ring

/-- Coarse but fully analytic hole allowance. This preserves the sharp target's
existing residual budget while avoiding an unnecessary optimization of the cutoff. -/
theorem logarithmic_hole_lower {c q : ℝ} (hc : 0 < c) (hq : 0 < q) (hqc : q ≤ c) :
    -(16 / 9) * c ≤ ∫ y in Ioc (0 : ℝ) c, F y * log (y / q) := by
  have hleft := (log_ratio_integrable hc hc).const_mul (16 / 9 : ℝ)
  have hright : IntegrableOn (fun y => F y * log (y / q)) (Ioc 0 c) :=
    (weighted_ratio_integrable hq).mono_set Ioc_subset_Ioi_self
  have hi : (∫ y in Ioc (0 : ℝ) c, (16 / 9 : ℝ) * log (y / c)) ≤
      ∫ y in Ioc (0 : ℝ) c, F y * log (y / q) := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hneg : log (y / c) ≤ 0 :=
      Real.log_nonpos (div_nonneg hy.1.le hc.le) ((div_le_one hc).mpr hy.2)
    have hle : log (y / c) ≤ log (y / q) := by
      apply Real.log_le_log (div_pos hy.1 hc)
      exact div_le_div_of_nonneg_left hy.1.le hq hqc
    by_cases hp : 0 ≤ log (y / q)
    · exact (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hneg).trans
        (mul_nonneg (F_nonneg y) hp)
    · have hp' : log (y / q) ≤ 0 := le_of_not_ge hp
      calc
        _ ≤ (16 / 9 : ℝ) * log (y / q) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        _ ≤ F y * log (y / q) := mul_le_mul_of_nonpos_right (F_mass y) hp'
  rw [integral_const_mul, log_ratio_self_integral hc] at hi
  linarith

/-- The complete main density integral is controlled by the two actual moments,
including the entire missing interval down to ordinate zero. -/
theorem truncated_ratio_integral_le {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hqc : q ≤ c) :
    (∫ y in Ioi c, F y * log (y / q)) ≤ M0 * log (1 / q) + M1 + (16 / 9) * c := by
  have hs := weighted_ratio_integrable hq
  have he : (∫ y in Ioi (0 : ℝ), F y * log (y / q)) =
      (∫ y in Ioc (0 : ℝ) c, F y * log (y / q)) +
        ∫ y in Ioi c, F y * log (y / q) := by
    rw [← Ioc_union_Ioi_eq_Ioi hc.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hs.mono_set Ioc_subset_Ioi_self) (hs.mono_set (Ioi_subset_Ioi hc.le))
  rw [full_ratio_integral hq] at he
  linarith [logarithmic_hole_lower hc hq hqc]

#print axioms F_integrable
#print axioms full_ratio_integral
#print axioms truncated_ratio_integral_le
end RHOcticPush.FourierMoments
