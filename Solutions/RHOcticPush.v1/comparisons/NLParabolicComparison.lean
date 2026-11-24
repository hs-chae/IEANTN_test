import OcticGeometry

/-! Exact scalar comparison with the retained written NL parabolic window in
RHExposureStudy.v1/locked/NL_RH/files/Intervals.md, “Parabolic window”.
This does not formalize that old analytic proof or change its source package.
The new octic theorem applies at the actual left endpoint only when that
endpoint additionally lies above exp(24). -/
namespace RHOcticPush.NLParabolicComparison
open Real
set_option maxHeartbeats 0

noncomputable def D (L : ℝ) : ℝ :=
  (243 / 200 : ℝ) * L - (93 / 100) * log L - 1 / 4
noncomputable def delta (L : ℝ) : ℝ := D L / exp (L / 2)
noncomputable def left (L : ℝ) : ℝ := exp (L - delta L)
noncomputable def right (L : ℝ) : ℝ := exp (L + delta L)
noncomputable def oldWidth (L : ℝ) : ℝ :=
  (right L - left L) / (sqrt (left L) * log (left L))
noncomputable def oldCountFactor (L : ℝ) : ℝ := (L + 1 / 25) / (L - delta L)
noncomputable def newCountFactor (L : ℝ) : ℝ := 1 + (21 / 5) / log (left L)

lemma log_twentyfour_lt : log (24 : ℝ) < 16 / 5 := by
  have he : (1359 / 500 : ℝ) < exp 1 := by linarith [exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 1359 / 500)
    (by norm_num : (16 : ℕ) ≠ 0)
  have hn : (24 : ℝ)^5 < (1359 / 500 : ℝ)^16 := by norm_num
  have hid : exp (16 / 5 : ℝ)^5 = exp 1^16 := by
    rw [← exp_nat_mul, ← exp_nat_mul]
    congr 1
    norm_num
  have hb : (24 : ℝ) < exp (16 / 5 : ℝ) := by
    by_contra h
    have hge := le_of_not_gt h
    have hpow := pow_le_pow_left₀ (exp_nonneg (16 / 5 : ℝ)) hge 5
    rw [hid] at hpow
    linarith
  exact (log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 24)).mpr hb

lemma log_tangent {L : ℝ} (hL : 24 ≤ L) :
    log L < (16 / 5 : ℝ) + L / 24 - 1 := by
  have h0 : 0 < L := by linarith
  have ht := log_le_sub_one_of_pos (div_pos h0 (by norm_num : (0 : ℝ) < 24))
  rw [log_div h0.ne' (by norm_num : (24 : ℝ) ≠ 0)] at ht
  linarith [log_twentyfour_lt]

lemma D_lower {L : ℝ} (hL : 24 ≤ L) : (27 / 25 : ℝ) * L < D L := by
  have hl := log_tangent hL
  unfold D
  linarith

lemma D_pos {L : ℝ} (hL : 24 ≤ L) : 0 < D L := by
  have h := D_lower hL
  nlinarith

lemma D_upper {L : ℝ} (hL : 24 ≤ L) : D L ≤ 2 * L := by
  have hl : 0 ≤ log L := log_nonneg (by linarith : (1 : ℝ) ≤ L)
  unfold D
  linarith

lemma delta_bounds {L : ℝ} (hL : 24 ≤ L) :
    0 < delta L ∧ delta L ≤ (3 / 10000 : ℝ) := by
  have h0 : 0 < L := by linarith
  have hd := D_pos hL
  have hu := D_upper hL
  have he := RHLimit.OcticGeometry.exp_half_lower hL
  have hb : D L ≤ (3 / 10000 : ℝ) * exp (L / 2) := by
    have hs : 0 ≤ L * (L - 24) := mul_nonneg h0.le (by linarith)
    nlinarith
  exact ⟨div_pos hd (exp_pos _), (div_le_iff₀ (exp_pos _)).mpr hb⟩

lemma left_log {L : ℝ} : log (left L) = L - delta L := by
  exact log_exp _

lemma left_sqrt {L : ℝ} : sqrt (left L) = exp ((L - delta L) / 2) := by
  exact (exp_half _).symm

lemma left_log_pos {L : ℝ} (hL : 24 ≤ L) : 0 < log (left L) := by
  rw [left_log]
  linarith [(delta_bounds hL).2]

lemma width_numerator_lower {L : ℝ} (hL : 24 ≤ L) :
    2 * D L * sqrt (left L) ≤ right L - left L := by
  have hd := D_pos hL
  have hδ := (delta_bounds hL).1
  have hs := self_le_sinh_iff.mpr hδ.le
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * exp L)
  have hid : right L - left L = 2 * exp L * sinh (delta L) := by
    simp only [right, left, sinh_eq, sub_eq_add_neg, exp_add]
    ring
  have hexp : exp L = exp (L / 2) * exp (L / 2) := by
    rw [← exp_add]
    congr 1
    ring
  have heq : 2 * exp L * delta L = 2 * D L * exp (L / 2) := by
    rw [hexp]
    unfold delta
    field_simp [exp_ne_zero]
    <;> ring
  have hb := exp_le_exp.mpr (by linarith : (L - delta L) / 2 ≤ L / 2)
  have hb' := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * D L)
  rw [← left_sqrt] at hb'
  rw [← hid, heq] at hm
  exact hb'.trans hm

/-- Entire old normalized width, not just its asymptotic coefficient. -/
theorem old_width_gt_216 {L : ℝ} (hL : 24 ≤ L) : (54 / 25 : ℝ) < oldWidth L := by
  have hl := D_lower hL
  have hδ := (delta_bounds hL).1
  have hx : 0 < sqrt (left L) := by rw [left_sqrt]; positivity
  have hlog := left_log_pos hL
  have hnum := width_numerator_lower hL
  have hcoef : (54 / 25 : ℝ) * log (left L) < 2 * D L := by
    rw [left_log]
    linarith
  have hmul := mul_lt_mul_of_pos_right hcoef hx
  unfold oldWidth
  apply (lt_div_iff₀ (mul_pos hx hlog)).mpr
  nlinarith

/-- The exact count coefficient improves at the identical actual left endpoint. -/
theorem new_count_factor_larger {L : ℝ} (hL : 24 ≤ L) :
    oldCountFactor L < newCountFactor L := by
  have hδ := (delta_bounds hL).2
  have hp : 0 < L - delta L := by linarith
  unfold oldCountFactor newCountFactor
  rw [left_log]
  apply (div_lt_iff₀ hp).mpr
  field_simp [hp.ne']
  linarith

/-- The octic width2.14891875 is strictly shorter than the full old window. -/
theorem new_interval_shorter {L : ℝ} (hL : 24 ≤ L) :
    left L + (343827 / 160000 : ℝ) * sqrt (left L) * log (left L) < right L := by
  have hw := old_width_gt_216 hL
  have hx : 0 < sqrt (left L) := by rw [left_sqrt]; positivity
  have hp := left_log_pos hL
  unfold oldWidth at hw
  have h := (lt_div_iff₀ (mul_pos hx hp)).mp hw
  have hc : (343827 / 160000 : ℝ) * (sqrt (left L) * log (left L)) <
      (54 / 25 : ℝ) * (sqrt (left L) * log (left L)) :=
    mul_lt_mul_of_pos_right (by norm_num) (mul_pos hx hp)
  nlinarith

/-- Both complete scalar objectives improve. Applicability of the arithmetic
new octic theorem additionally requires exp24<=left L; it is not asserted for
all L>=24, since left24<exp24. -/
theorem matched_scalar_comparison {L : ℝ} (hL : 24 ≤ L) :
    left L + (343827 / 160000 : ℝ) * sqrt (left L) * log (left L) < right L ∧
    oldCountFactor L < newCountFactor L :=
  ⟨new_interval_shorter hL, new_count_factor_larger hL⟩

end RHOcticPush.NLParabolicComparison

#print axioms RHOcticPush.NLParabolicComparison.log_twentyfour_lt
#print axioms RHOcticPush.NLParabolicComparison.log_tangent
#print axioms RHOcticPush.NLParabolicComparison.D_lower
#print axioms RHOcticPush.NLParabolicComparison.D_pos
#print axioms RHOcticPush.NLParabolicComparison.D_upper
#print axioms RHOcticPush.NLParabolicComparison.delta_bounds
#print axioms RHOcticPush.NLParabolicComparison.left_log
#print axioms RHOcticPush.NLParabolicComparison.left_sqrt
#print axioms RHOcticPush.NLParabolicComparison.left_log_pos
#print axioms RHOcticPush.NLParabolicComparison.width_numerator_lower
#print axioms RHOcticPush.NLParabolicComparison.old_width_gt_216
#print axioms RHOcticPush.NLParabolicComparison.new_count_factor_larger
#print axioms RHOcticPush.NLParabolicComparison.new_interval_shorter
#print axioms RHOcticPush.NLParabolicComparison.matched_scalar_comparison
