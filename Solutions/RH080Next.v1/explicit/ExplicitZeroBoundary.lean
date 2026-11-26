/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSZeroSource

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit

private theorem log_div_tendsto_zero : Tendsto (fun T : ℝ => log T/T) atTop (𝓝 0) := by
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero

private theorem scaled_amplitude_tail (F : ℝ → ℝ) (g Δ T : ℝ)
    (hΔ : 0 < Δ) (hT : 0 < T) (htail : ∀ u : ℝ, u ≠ 0 → |F u| ≤ g/u^2) :
    Δ*|F (Δ*T)| ≤ (g/Δ)/T^2 := by
  have h := mul_le_mul_of_nonneg_left (htail (Δ*T) (mul_ne_zero hΔ.ne' hT.ne')) hΔ.le
  calc
    Δ*|F (Δ*T)| ≤ Δ*(g/(Δ*T)^2) := h
    _ = (g/Δ)/T^2 := by field_simp <;> ring

/-- The infinity boundary term against N−Q really vanishes for the actual
quadratic Fourier decay. It is not an unverified Stieltjes endpoint premise. -/
theorem zero_remainder_boundary_tendsto (hcount : SourceCMSZeroCounting)
    (F : ℝ → ℝ) (g Δ : ℝ) (hg : 0 ≤ g) (hΔ : 0 < Δ)
    (htail : ∀ u : ℝ, u ≠ 0 → |F u| ≤ g/u^2) :
    Tendsto (fun T : ℝ => Δ*|F (Δ*T)| *cmsCountRemainder T) atTop (𝓝 0) := by
  let B := g/Δ
  let a : ℝ → ℝ := fun T => B*((3/20:ℝ)*(log T/T)*(1/T)+3*(1/T)^2)
  have hi : Tendsto (fun T : ℝ => 1/T) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a,mul_zero,zero_mul,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] using
      (((log_div_tendsto_zero.const_mul (3/20)).mul hi).add ((hi.pow 2).const_mul 3)).const_mul B
  apply squeeze_zero_norm' _ ha
  filter_upwards [eventually_ge_atTop (exp 1),eventually_ge_atTop (1:ℝ)] with T he hT
  have hT0 : 0 < T := by linarith
  have hf := scaled_amplitude_tail F g Δ T hΔ hT0 htail
  have hb := hcount.2.2 T he
  have hpos : 0 ≤ Δ*|F (Δ*T)| := by positivity
  calc
    ‖Δ*|F (Δ*T)| *cmsCountRemainder T‖ = (Δ*|F (Δ*T)|)*|cmsCountRemainder T| := by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hpos]
    _ ≤ (B/T^2)*((3/20:ℝ)*log T+3) :=
      mul_le_mul hf hb (abs_nonneg _) (by dsimp [B]; positivity)
    _ = a T := by dsimp [a]; field_simp <;> ring

/-- The independent infinity boundary term against the full comparison
function Q also vanishes. Its T log T growth is retained in the proof. -/
theorem zero_main_boundary_tendsto (F : ℝ → ℝ) (g Δ : ℝ)
    (hg : 0 ≤ g) (hΔ : 0 < Δ)
    (htail : ∀ u : ℝ, u ≠ 0 → |F u| ≤ g/u^2) :
    Tendsto (fun T : ℝ => Δ*|F (Δ*T)| *cmsQ T) atTop (𝓝 0) := by
  let B := g/Δ
  let c := |log (2*π*exp 1)|
  let a : ℝ → ℝ := fun T => B*(((log T/T)+c*(1/T))/(2*π)+(7/8:ℝ)*(1/T)^2)
  have hi : Tendsto (fun T : ℝ => 1/T) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a,mul_zero,zero_mul,zero_pow (by norm_num : (2:ℕ)≠0),add_zero,zero_div] using
      (((log_div_tendsto_zero.add (hi.const_mul c)).div_const (2*π)).add
        ((hi.pow 2).const_mul (7/8))).const_mul B
  apply squeeze_zero_norm' _ ha
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  have hlogT := log_nonneg hT
  have hf := scaled_amplitude_tail F g Δ T hΔ hT0 htail
  have hQ : |cmsQ T| ≤ T/(2*π)*(log T+c)+7/8 := by
    have hl : |log (T/(2*π*exp 1))| ≤ log T+c := by
      rw [log_div hT0.ne' (by positivity)]
      have h := abs_sub (log T) (log (2*π*exp 1))
      simpa only [abs_of_nonneg hlogT,c] using h
    unfold cmsQ
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ T/(2*π))]
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ T/(2*π))
    norm_num
    linarith
  have hpos : 0 ≤ Δ*|F (Δ*T)| := by positivity
  calc
    ‖Δ*|F (Δ*T)| *cmsQ T‖ = (Δ*|F (Δ*T)|)*|cmsQ T| := by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hpos]
    _ ≤ (B/T^2)*(T/(2*π)*(log T+c)+7/8) :=
      mul_le_mul hf hQ (abs_nonneg _) (by dsimp [B]; positivity)
    _ = a T := by dsimp [a]; field_simp <;> ring

#print axioms zero_remainder_boundary_tendsto
#print axioms zero_main_boundary_tendsto
end RH080Next.Explicit
