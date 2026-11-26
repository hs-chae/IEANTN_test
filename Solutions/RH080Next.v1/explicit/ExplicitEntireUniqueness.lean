/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RH080Next.Explicit

/-- Uniqueness of the entire extension from its actual real-axis values. -/
theorem entire_eq_of_real_eq (F G : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) (hreal : ∀ u : ℝ, F (u:ℂ) = G (u:ℂ)) : F = G := by
  have hFa : AnalyticOnNhd ℂ F univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  have hGa : AnalyticOnNhd ℂ G univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hG
  let u : ℕ → ℂ := fun n => 1/((n:ℂ)+1)
  have hu : Tendsto u atTop (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · filter_upwards with n
      simp only [u, mem_compl_iff, mem_singleton_iff]
      apply div_ne_zero one_ne_zero
      have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
      exact_mod_cast hn.ne'
  have hf : ∀ᶠ n : ℕ in atTop, F (u n) = G (u n) := by
    filter_upwards with n
    have h := hreal (1/((n:ℝ)+1))
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_natCast] using h
  exact hFa.eq_of_frequently_eq hGa (hu.frequently hf.frequently)

end RH080Next.Explicit
