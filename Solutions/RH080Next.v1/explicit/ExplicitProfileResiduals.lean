/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitProfileScalars

set_option autoImplicit false
noncomputable section
open Real Set
namespace RH080Next.Explicit

theorem fap_denominator_lower (F0 J : ℝ)
    (hF : (999999999/1000000000:ℝ) ≤ F0) (hJ : J ≤ (20371547/1000000000:ℝ)) :
    (574071/625000:ℝ) ≤ F0-explicitPenalty*J := by
  unfold explicitPenalty
  nlinarith

theorem w4_denominator_lower (F0 J : ℝ)
    (hF : (999999999/1000000000:ℝ) ≤ F0) (hJ : J ≤ (2559477/125000000:ℝ)) :
    (1836193/2000000:ℝ) ≤ F0-explicitPenalty*J := by
  unfold explicitPenalty
  nlinarith

private theorem residual_cap_mono (c t D0 D U K K0 : ℝ)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hD : D0 ≤ D) (hK : K ≤ K0) :
    explicitResidual c D0 U K0 t ≤ explicitResidual c D U K t := by
  have hm := mul_le_mul_of_nonneg_right hD (mul_nonneg hc ht)
  unfold explicitResidual
  nlinarith

/-- The complete original Fap 0.8 slab, by proved concavity and exact
rational/Taylor endpoint enclosures, with upward-rounded numerical caps. -/
theorem fap_08_residual (D K t : ℝ)
    (hD : (574071/625000:ℝ) ≤ D) (hK : K ≤ -(1939/2500:ℝ))
    (ht : t ∈ Icc (42:ℝ) 174) :
    (1/1000000:ℝ) ≤ explicitResidual (4/5) D (3909/5000) K t := by
  have hleft : (1/1000000:ℝ) ≤ explicitResidual (4/5) (574071/625000) (3909/5000) (-(1939/2500)) 42 := by
    norm_num [explicitResidual]
    nlinarith [log_slab_left_lower]
  have hright : (1/1000000:ℝ) ≤ explicitResidual (4/5) (574071/625000) (3909/5000) (-(1939/2500)) 174 := by
    norm_num [explicitResidual]
    nlinarith [log_slab_right_lower]
  have hslab := explicitResidual_slab_lower (4/5) (574071/625000) (3909/5000) (-(1939/2500)) 42 174 t
    (by norm_num) (by norm_num) (by norm_num) ht
  exact (le_min hleft hright).trans (hslab.trans
    (residual_cap_mono _ _ _ _ _ _ _ (by norm_num) (by linarith [ht.1]) hD hK))

theorem fap_074_residual (D K t : ℝ)
    (hD : (574071/625000:ℝ) ≤ D) (hK : K ≤ -(1939/2500:ℝ))
    (ht : t ∈ Icc (42:ℝ) 63) :
    (1/1000000:ℝ) ≤ explicitResidual (37/50) D (3909/5000) K t := by
  have hleft : (1/1000000:ℝ) ≤ explicitResidual (37/50) (574071/625000) (3909/5000) (-(1939/2500)) 42 := by
    norm_num [explicitResidual]
    nlinarith [two_le_log_of_fifteen_le (777/50) (by norm_num)]
  have hright : (1/1000000:ℝ) ≤ explicitResidual (37/50) (574071/625000) (3909/5000) (-(1939/2500)) 63 := by
    norm_num [explicitResidual]
    nlinarith [log_074_right_lower]
  have hslab := explicitResidual_slab_lower (37/50) (574071/625000) (3909/5000) (-(1939/2500)) 42 63 t
    (by norm_num) (by norm_num) (by norm_num) ht
  exact (le_min hleft hright).trans (hslab.trans
    (residual_cap_mono _ _ _ _ _ _ _ (by norm_num) (by linarith [ht.1]) hD hK))

theorem fap_075_residual (D K t : ℝ)
    (hD : (574071/625000:ℝ) ≤ D) (hK : K ≤ -(1939/2500:ℝ))
    (ht : t ∈ Icc (42:ℝ) 70) :
    (1/1000000:ℝ) ≤ explicitResidual (3/4) D (3909/5000) K t := by
  have hleft : (1/1000000:ℝ) ≤ explicitResidual (3/4) (574071/625000) (3909/5000) (-(1939/2500)) 42 := by
    norm_num [explicitResidual]
    nlinarith [two_le_log_of_fifteen_le (63/4) (by norm_num)]
  have hright : (1/1000000:ℝ) ≤ explicitResidual (3/4) (574071/625000) (3909/5000) (-(1939/2500)) 70 := by
    norm_num [explicitResidual]
    nlinarith [log_075_right_lower]
  have hslab := explicitResidual_slab_lower (3/4) (574071/625000) (3909/5000) (-(1939/2500)) 42 70 t
    (by norm_num) (by norm_num) (by norm_num) ht
  exact (le_min hleft hright).trans (hslab.trans
    (residual_cap_mono _ _ _ _ _ _ _ (by norm_num) (by linarith [ht.1]) hD hK))

/-- The whole w4 ray has a rigorously positive leading slope; no sampled
logarithmic upper endpoint or optimality assumption is used. -/
theorem w4_ray_residual (D K t : ℝ)
    (hD : (1836193/2000000:ℝ) ≤ D) (hK : K ≤ 0) (ht : 42 ≤ t) :
    (1/1000000:ℝ) ≤ explicitResidual (425531/500000) D (19533921/25000000) K t := by
  have hleft : (1/1000000:ℝ) ≤ explicitResidual (425531/500000) (1836193/2000000) (19533921/25000000) 0 42 := by
    norm_num [explicitResidual]
    nlinarith [two_le_log_of_fifteen_le (8936151/500000) (by norm_num)]
  have hslope : (0:ℝ) ≤ (425531/500000)*(1836193/2000000)-(19533921/25000000) := by norm_num
  have hmono := explicitResidual_monotone_ray (425531/500000) (1836193/2000000) (19533921/25000000) 0
    (by norm_num) (by norm_num) hslope
  have hRay := hmono (show (42:ℝ) ∈ Ioi (0:ℝ) by norm_num) (show t ∈ Ioi (0:ℝ) by change 0 < t; linarith) ht
  exact hleft.trans (hRay.trans (residual_cap_mono _ _ _ _ _ _ _ (by norm_num) (by linarith) hD hK))

#print axioms fap_08_residual
#print axioms fap_074_residual
#print axioms fap_075_residual
#print axioms w4_ray_residual
end RH080Next.Explicit
