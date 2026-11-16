/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.DirectKernelFinite

open Complex MeasureTheory Set Filter
namespace WinnerDirectKernel

noncomputable def logResidual (R : ℝ → ℝ) (v L : ℝ) : ℝ :=
  R L/L + ∫ u in v..L, R u/u^2

/-- A generic CHJ-sized finite-formula remainder propagates without the triangle density loss. -/
theorem finite_formula_residual {ι : Type*} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ)
    (R : ℝ → ℝ) {M T v L : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (hv : 0 < v) (hL : v ≤ L)
    (hR : IntervalIntegrable (fun u : ℝ => R u/u^2) volume v L)
    (hExplicit : ∀ u ∈ Set.Icc v L,
      |R u + (zeroSum S z w u).re| ≤ M*Real.exp u*u/T) :
    |logResidual R v L| ≤
      ‖∑ i ∈ S, (w i : ℂ)*piKernel (z i) v L‖ +
        (M*Real.exp L/T)*(1+1/v) := by
  let Q : ℝ → ℝ := fun u => R u + (zeroSum S z w u).re
  have hLp : 0 < L := hv.trans_le hL
  have hqi : IntervalIntegrable (fun u : ℝ => Q u/u^2) volume v L := by
    have hz := (zero_sum_integrable S z w hv hL)
    have hzr : IntervalIntegrable (fun u : ℝ => (zeroSum S z w u).re/u^2) volume v L := by
      have hc : Continuous (fun u : ℝ => (zeroSum S z w u).re) := by
        unfold zeroSum zexp
        fun_prop
      apply ContinuousOn.intervalIntegrable_of_Icc hL
      apply hc.continuousOn.div (by fun_prop)
      intro u hu
      exact pow_ne_zero 2 (hv.trans_le hu.1).ne'
    simpa only [Q, add_div] using hR.add hzr
  have hlead : |Q L/L| ≤ M*Real.exp L/T := by
    rw [abs_div, abs_of_pos hLp]
    have he := hExplicit L ⟨hL, le_rfl⟩
    apply (div_le_iff₀ hLp).mpr
    dsimp [Q]
    calc _ ≤ M*Real.exp L*L/T := he
         _ = _ := by ring
  have hpoint : ∀ u ∈ Set.Ioc v L,
      |Q u/u^2| ≤ (M/(T*v))*Real.exp u := by
    intro u hu
    have hu0 : 0 < u := hv.trans hu.1
    have he := hExplicit u ⟨hu.1.le,hu.2⟩
    rw [abs_div, abs_of_nonneg (sq_nonneg u)]
    have hfirst : |Q u|/u^2 ≤ (M*Real.exp u)/(T*u) := by
      apply (div_le_iff₀ (pow_pos hu0 2)).mpr
      dsimp [Q]
      calc _ ≤ M*Real.exp u*u/T := he
           _ = _ := by field_simp <;> ring
    calc _ ≤ (M*Real.exp u)/(T*u) := hfirst
         _ ≤ (M*Real.exp u)/(T*v) := by
           apply div_le_div_of_nonneg_left (by positivity) (by positivity)
           exact mul_le_mul_of_nonneg_left hu.1.le hT.le
         _ = _ := by ring
  have hib : IntervalIntegrable (fun u : ℝ => (M/(T*v))*Real.exp u) volume v L := by
    apply Continuous.intervalIntegrable; fun_prop
  have hn := intervalIntegral.norm_integral_le_of_norm_le (f := fun u : ℝ => Q u/u^2) hL
    (Eventually.of_forall (fun u hu => by simpa only [Real.norm_eq_abs] using hpoint u hu)) hib
  have hint : |∫ u in v..L, Q u/u^2| ≤ M*Real.exp L/(T*v) := by
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hn
    have hexp : (∫ u in v..L, Real.exp u) ≤ Real.exp L := by
      simpa using integral_exp_upper (v := v) (L := L) (by norm_num : (0:ℝ)<1)
    calc _ ≤ (M/(T*v))*(∫ u in v..L, Real.exp u) := hn
         _ ≤ (M/(T*v))*Real.exp L := mul_le_mul_of_nonneg_left hexp (by positivity)
         _ = _ := by ring
  have hq : |Q L/L + (∫ u in v..L, Q u/u^2)| ≤ (M*Real.exp L/T)*(1+1/v) := by
    have ht := abs_add_le (Q L/L) (∫ u in v..L, Q u/u^2)
    have he : M*Real.exp L/T + M*Real.exp L/(T*v) = (M*Real.exp L/T)*(1+1/v) := by
      field_simp <;> ring
    linarith
  have hzreal := integrated_zeroSum_re S z w hv hL
  have hsum : logResidual R v L + (∑ i ∈ S, (w i : ℂ)*piKernel (z i) v L).re =
      Q L/L + (∫ u in v..L, Q u/u^2) := by
    rw [← hzreal]
    dsimp [logResidual,Q]
    rw [show (fun u : ℝ => (R u+(zeroSum S z w u).re)/u^2) =
      (fun u : ℝ => R u/u^2+(zeroSum S z w u).re/u^2) by funext u; ring]
    have hzri : IntervalIntegrable (fun u : ℝ => (zeroSum S z w u).re/u^2) volume v L := by
      have h := hqi.sub hR
      convert h using 1
      funext u
      dsimp [Q]
      ring
    rw [intervalIntegral.integral_add hR hzri]
    ring
  have htri := abs_sub (Q L/L + (∫ u in v..L, Q u/u^2))
    (∑ i ∈ S, (w i : ℂ)*piKernel (z i) v L).re
  have heq : logResidual R v L =
      Q L/L + (∫ u in v..L, Q u/u^2) - (∑ i ∈ S, (w i : ℂ)*piKernel (z i) v L).re := by
    linarith
  rw [heq]
  have hr := Complex.abs_re_le_norm (∑ i ∈ S, (w i : ℂ)*piKernel (z i) v L)
  linarith

#print axioms finite_formula_residual
end WinnerDirectKernel
