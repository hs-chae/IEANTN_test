/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitDomain
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false
noncomputable section
open Real Set
namespace RH080Next.Explicit

def explicitResidual (c D U K t : ℝ) : ℝ :=
  (c*D-U)*t/2+U*log (c*t/2)-K

private theorem residual_linear_log (c D U K t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    explicitResidual c D U K t = ((c*D-U)/2)*t+U*log t+(U*log (c/2)-K) := by
  unfold explicitResidual
  rw [show c*t/2 = (c/2)*t by ring,log_mul (by positivity : c/2≠0) ht.ne']
  ring

theorem explicitResidual_concave (c D U K : ℝ) (hc : 0 < c) (hU : 0 ≤ U) :
    ConcaveOn ℝ (Ioi (0:ℝ)) (explicitResidual c D U K) := by
  have hlin : ConcaveOn ℝ (Ioi (0:ℝ)) (fun t : ℝ => ((c*D-U)/2)*t) := by
    refine ⟨convex_Ioi _,?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    exact le_of_eq (by ring)
  have hlog : ConcaveOn ℝ (Ioi (0:ℝ)) (fun t : ℝ => U*log t) := by
    simpa only [smul_eq_mul] using ConcaveOn.smul hU strictConcaveOn_log_Ioi.concaveOn
  apply ((hlin.add hlog).add_const (U*log (c/2)-K)).congr
  intro t ht
  exact (residual_linear_log c D U K t hc ht).symm

/-- Exact continuous-slab minimum principle. Endpoint computations alone are
used only after this concavity theorem, not as a sampled-domain heuristic. -/
theorem explicitResidual_slab_lower (c D U K a b t : ℝ) (hc : 0 < c)
    (hU : 0 ≤ U) (ha : 0 < a) (ht : t ∈ Icc a b) :
    min (explicitResidual c D U K a) (explicitResidual c D U K b) ≤
      explicitResidual c D U K t := by
  exact (explicitResidual_concave c D U K hc hU).min_le_of_mem_Icc ha
    (lt_of_lt_of_le ha (ht.1.trans ht.2)) ht

theorem explicitResidual_monotone_ray (c D U K : ℝ) (hc : 0 < c)
    (hU : 0 ≤ U) (hSlope : 0 ≤ c*D-U) :
    MonotoneOn (explicitResidual c D U K) (Ioi (0:ℝ)) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  have hlin := mul_le_mul_of_nonneg_left hab hSlope
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity : 0 < c*a/2)
      (by nlinarith : c*a/2 ≤ c*b/2)) hU
  unfold explicitResidual
  linarith

/-- A tiny positive residual already forces more than one half-open prime,
throughout the full log-domain. This is the quantitative margin needed to
remove a possible prime at the upper endpoint. -/
theorem count_gt_one_of_residual (t M k r : ℝ) (ht : 42 ≤ t)
    (hM0 : 0 ≤ M) (hM : M ≤ 2) (hr : (1/1000000:ℝ) ≤ r)
    (hcount : r ≤ M*t*exp (-t/2)*k) : 1 < k := by
  have hte := polynomial_exp_decay t ht 1 (by norm_num) (by norm_num)
  norm_num at hte
  have he := exp_neg_twenty_one_upper
  have ht0 : 0 ≤ t := by linarith
  have hcoef0 : 0 ≤ M*t*exp (-t/2) := by positivity
  have hcoef : M*t*exp (-t/2) < (1/1000000:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hte hM0
    have hM' := mul_le_mul_of_nonneg_right hM (exp_pos (-21)).le
    nlinarith
  by_contra hh
  have hk : k ≤ 1 := le_of_not_gt hh
  have hm := mul_le_mul_of_nonneg_left hk hcoef0
  nlinarith

#print axioms explicitResidual_slab_lower
#print axioms explicitResidual_monotone_ray
#print axioms count_gt_one_of_residual
end RH080Next.Explicit
