/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticCoverage

namespace RHLimit.OcticGeometry
open Real Set MeasureTheory
set_option maxHeartbeats 2000000

theorem trivial_cost_family (n : ℕ) {C : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) :
    EvenKernel.TrivialCost n C (1 / 1000) := by
  intro L hL
  let a := EvenKernel.a C L
  let b := EvenKernel.b C L
  let f : ℝ → ℝ := fun t => EvenKernel.kernel n ((log t - L) / EvenKernel.δ C L) /
    (sqrt t * t * (t ^ 2 - 1))
  have ha : (24 : ℝ) ≤ a := a_ge_twenty_four hC hL
  have ha0 : 0 < a := by linarith
  have hb : b ≤ 3 * a := b_le_three_a hC hL
  have hab : a ≤ b := by
    have hd := delta_nonneg hC.1 hL
    dsimp [a, b, EvenKernel.a, EvenKernel.b]
    apply Real.exp_le_exp.mpr
    linarith
  have hδ0 : 0 < EvenKernel.δ C L := by
    have hd := D_family_lower hC.1 hL
    unfold EvenKernel.δ
    exact mul_pos (by linarith : 0 < EvenKernel.D C L) (exp_pos _)
  have hc : ContinuousOn f (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht24 : (24 : ℝ) ≤ t := ha.trans ht.1
    have ht0 : 0 < t := by linarith
    have hs0 : sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    have htne : t ≠ 0 := ht0.ne'
    have hsq : t ^ 2 - 1 ≠ 0 := by nlinarith
    have hden : sqrt t * t * (t ^ 2 - 1) ≠ 0 := mul_ne_zero (mul_ne_zero hs0 htne) hsq
    dsimp [f, EvenKernel.kernel]
    fun_prop (disch := first | assumption | exact hδ0.ne')
  have hpoint : ∀ t ∈ Icc a b, f t ≤ 1 / (2300 * a) := by
    intro t ht
    have ht24 : (24 : ℝ) ≤ t := ha.trans ht.1
    have ht0 : 0 < t := by linarith
    have hst : (4 : ℝ) ≤ sqrt t := by
      have hh := Real.sqrt_le_sqrt (show (16 : ℝ) ≤ t by linarith)
      norm_num at hh
      exact hh
    have hsq : (575 : ℝ) ≤ t ^ 2 - 1 := by nlinarith
    have hm1 := mul_le_mul_of_nonneg_right hst ht0.le
    have hm2 := mul_le_mul hm1 hsq (by norm_num : (0 : ℝ) ≤ 575)
      (show 0 ≤ sqrt t * t by positivity)
    have hden : 2300 * a ≤ sqrt t * t * (t ^ 2 - 1) := by nlinarith [ht.1]
    have hden0 : 0 < sqrt t * t * (t ^ 2 - 1) :=
      (by positivity : (0 : ℝ) < 2300 * a).trans_le hden
    have hk := EvenKernel.kernel_le_one n ((log t - L) / EvenKernel.δ C L)
    dsimp [f]
    calc
      _ ≤ 1 / (sqrt t * t * (t ^ 2 - 1)) := div_le_div_of_nonneg_right hk hden0.le
      _ ≤ 1 / (2300 * a) := one_div_le_one_div_of_le (by positivity) hden
  change (∫ t in a..b, f t) ≤ 1 / 1000
  calc
    (∫ t in a..b, f t) ≤ ∫ t in a..b, (1 / (2300 * a) : ℝ) :=
      intervalIntegral.integral_mono_on hab hc.intervalIntegrable intervalIntegrable_const hpoint
    _ = (b - a) / (2300 * a) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ (2 * a) / (2300 * a) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / 1150 := by
      field_simp [ha0.ne'] <;> norm_num
    _ ≤ 1 / 1000 := by norm_num

theorem trivial_cost_215 : EvenKernel.TrivialCost 4 (43 / 20) (1 / 1000) :=
  trivial_cost_family 4 (by norm_num)

/-- The original actual-prime conclusion now needs only three analytic contracts. -/
theorem prime_count_215_three_inputs (rh : RiemannHypothesis)
    (hef : EvenKernel.ExplicitFormula 4 (43 / 20))
    (hz : EvenKernel.ZeroEstimate 4 (43 / 20) (911 / 500) (3 / 2) (3 / 125))
    (hpp : EvenKernel.PrimePowerCost 4 (43 / 20) (31 / 2000)) :
    ∀ u : ℝ, Real.exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + 43 / 20 * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u :=
  prime_count_215_reduced rh hef hz hpp trivial_cost_215

#print axioms trivial_cost_family
#print axioms prime_count_215_three_inputs
end RHLimit.OcticGeometry
