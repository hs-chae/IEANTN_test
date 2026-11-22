import ActualConsumer
namespace Ramanujan640
open Real IEANTN
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

noncomputable def q (z : ℝ) : ℝ := 39/20+(39/10)/z+(39/2)/z^2
noncomputable def p3 (z : ℝ) : ℝ := 1+1/z+2/z^2+6/z^3

theorem exp42_source_cap : exp (42:ℝ) ≤ (10:ℝ)^19 := by
  interval_decide 100 (trust := kernel)

theorem source_deficit_upper (hB : Buthe.v1.theorem_2_li_minus_pi)
    {z : ℝ} (hz : 0 < z) (h2 : 2 ≤ exp z) (h42 : z ≤ 42) :
    deficit z ≤ q z := by
  have hcap : exp z ≤ (10:ℝ)^19 :=
    (Real.exp_le_exp.mpr h42).trans exp42_source_cap
  have h := hB (exp z) h2 hcap
  rw [← exp_half, log_exp] at h
  have hp : 0 ≤ z/exp (z/2) := by positivity
  have hm := mul_le_mul_of_nonneg_right h hp
  have heL : (li (exp z)-primeCounting (exp z))*(z/exp (z/2)) = deficit z := by
    unfold deficit
    ring
  have heR : exp (z/2)/z*(1.95+3.9/z+19.5/z^2)*(z/exp (z/2)) = q z := by
    unfold q
    norm_num
    field_simp [hz.ne', exp_ne_zero]
    <;> ring
  rw [heL, heR] at hm
  exact hm

theorem source_deficit_pos (hB : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hz : 0 < z) (h2 : 2 ≤ exp z) (h42 : z ≤ 42) :
    0 < deficit z := by
  unfold deficit
  exact div_pos (mul_pos (hB (exp z) h2
    ((Real.exp_le_exp.mpr h42).trans exp42_source_cap)) hz) (exp_pos _)

theorem primePart_square_actual {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 42) :
    RamStudy.count (z/2) ≤ primePart z := by
  have h := primePart_square_lower hz0 hz
  unfold RamStudy.count
  convert h using 1 <;> field_simp <;> ring

theorem primePart_lower_from_source (hB : Buthe.v1.theorem_2_li_minus_pi)
    {z : ℝ} (hz : 0 < z) (h42 : z ≤ 42) (hroot : 2 ≤ exp (z/2))
    (hw : p3 (z/2) ≤ RamStudy.w (z/2)) :
    p3 (z/2)-q (z/2)*exp (-z/4) ≤ primePart z := by
  have hd := source_deficit_upper hB (by linarith : 0 < z/2) hroot (by linarith : z/2 ≤ 42)
  have hc := actual_count_lower hd
  have hp := primePart_square_actual hz.le h42
  have he : exp (-(z/2)/2)=exp (-z/4) := by congr 1;ring
  rw [he] at hc
  linarith

/-- Uniform prime-count upper bound derived from the finite published sign
and an independently proved global logarithmic-integral barrier. -/
theorem count_upper_of_global_w (hB : Buthe.v1.theorem_2_li_gt_pi)
    {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ s : ℝ, 0 < s → RamStudy.w s ≤ M)
    {s : ℝ} (hs : 0 < s) (hs42 : s ≤ 42) :
    primeCounting (exp s) ≤ M*exp s/s := by
  by_cases h2 : 2 ≤ exp s
  · have hp : primeCounting (exp s) ≤ li (exp s) := by
      linarith [hB (exp s) h2 ((Real.exp_le_exp.mpr hs42).trans exp42_source_cap)]
    have hh := hw s hs
    unfold RamStudy.w at hh
    have hf := mul_le_mul_of_nonneg_right hh (show 0 ≤ exp s/s by positivity)
    have he : s/exp s*li (exp s)*(exp s/s)=li (exp s) := by
      field_simp [hs.ne']
    rw [he] at hf
    exact hp.trans (by convert hf using 1 <;> ring)
  · rw [primeCounting_zero_of_lt_two (exp_pos s).le (lt_of_not_ge h2)]
    positivity

#print axioms source_deficit_upper
#print axioms source_deficit_pos
#print axioms primePart_lower_from_source
#print axioms count_upper_of_global_w
end Ramanujan640
