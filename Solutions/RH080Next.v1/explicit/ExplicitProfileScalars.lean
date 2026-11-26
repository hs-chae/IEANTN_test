/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitErrorBudget
import ExplicitAffineSignedMoment
import ExplicitScalarLogBounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private def safeSignedCap (V mu : ℝ) : ℝ :=
  V/(2*(6283/2000:ℝ)^2)-2*(999999999/1000000000:ℝ)*(3/8)*(1+613/625)+
    40*mu*(3/8:ℝ)^3*(1/9+(9809/10000:ℝ)/3)

/-- Analytic rounding of the actual signed moment from source-driven finite
nodal data. The cutoff logarithm and pi inequalities are kernel theorems. -/
theorem nodal_signed_cap (nodes : List ℚ) (m : ℕ) (V mu : ℝ)
    (hF0 : (999999999/1000000000:ℝ) ≤ nodalF0 nodes m)
    (hV : nodalV1 nodes m ≤ V) (hV0 : 0 ≤ V)
    (hMu : nodalMu2Upper nodes m ≤ mu) (hMu0 : 0 ≤ mu) :
    nodalSignedLogUpper nodes m (3/8) ≤ safeSignedCap V mu := by
  obtain ⟨hloglo,hloghi⟩ := log_three_eighths_bounds
  have hF00 : 0 ≤ nodalF0 nodes m := by linarith
  have hV10 : 0 ≤ nodalV1 nodes m := by unfold nodalV1; positivity
  have hpi : (6283/2000:ℝ) ≤ π := by linarith [pi_gt_d4]
  have hden : 2*(6283/2000:ℝ)^2 ≤ 2*π^2 := by nlinarith [pi_pos]
  have hvt := (div_le_div_of_nonneg_left hV10 (by norm_num : (0:ℝ)<2*(6283/2000:ℝ)^2) hden).trans
    (div_le_div_of_nonneg_right hV (by norm_num : (0:ℝ)≤2*(6283/2000:ℝ)^2))
  have hcenter := mul_le_mul hF0 (show (1+613/625:ℝ) ≤ 1-log (3/8:ℝ) by linarith)
    (by norm_num : (0:ℝ)≤1+613/625) hF00
  have hcoeff0 : 0 ≤ (1/9:ℝ)-log (3/8:ℝ)/3 := by linarith
  have hcoeff : (1/9:ℝ)-log (3/8:ℝ)/3 ≤ 1/9+(9809/10000:ℝ)/3 := by linarith
  have hmut := mul_le_mul hMu hcoeff hcoeff0 hMu0
  unfold nodalSignedLogUpper safeSignedCap
  nlinarith

theorem fap_signed_cap (nodes : List ℚ) (m : ℕ)
    (hF0 : (999999999/1000000000:ℝ) ≤ nodalF0 nodes m)
    (hV : nodalV1 nodes m ≤ (507714/125000:ℝ))
    (hMu : nodalMu2Upper nodes m ≤ (30963/125000:ℝ)) :
    nodalSignedLogUpper nodes m (3/8) ≤ -(10509/10000:ℝ) := by
  have h := nodal_signed_cap nodes m _ _ hF0 hV (by norm_num) hMu (by norm_num)
  have hcap : safeSignedCap (507714/125000) (30963/125000) ≤ -(10509/10000:ℝ) := by norm_num [safeSignedCap]
  exact h.trans hcap

theorem w4_signed_cap (nodes : List ℚ) (m : ℕ)
    (hF0 : (999999999/1000000000:ℝ) ≤ nodalF0 nodes m)
    (hV : nodalV1 nodes m ≤ (509/125:ℝ))
    (hMu : nodalMu2Upper nodes m ≤ (249/1000:ℝ)) :
    nodalSignedLogUpper nodes m (3/8) ≤ -(26/25:ℝ) := by
  have h := nodal_signed_cap nodes m _ _ hF0 hV (by norm_num) hMu (by norm_num)
  have hcap : safeSignedCap (509/125) (249/1000) ≤ -(26/25:ℝ) := by norm_num [safeSignedCap]
  exact h.trans hcap

/-- A shared safe constant for all three locked Fap slab coefficients.
The exact k=16 denominator is retained; only proved upward rounding is used. -/
theorem fap_constant_cap (c J H S : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ (4/5:ℝ))
    (hJ0 : 0 ≤ J) (hJ : J ≤ (20371547/1000000000:ℝ))
    (hH0 : 0 ≤ H) (hH : H ≤ (57139/500000:ℝ))
    (hS : S ≤ -(10509/10000:ℝ)) :
    explicitConstant c J H S 16 ≤ -(1939/2500:ℝ) := by
  let qlo : ℝ := 1-2*(13863/5000:ℝ)/42
  have hqlo : 0 < qlo := by dsimp [qlo]; norm_num
  have hlog0 : 0 ≤ log (16:ℝ) := log_nonneg (by norm_num)
  have hq : qlo ≤ mvBlockDenom 16 42 := by
    unfold mvBlockDenom
    dsimp [qlo]
    linarith [log_sixteen_upper]
  have hq0 : 0 < mvBlockDenom 16 42 := hqlo.trans_le hq
  have hnum1 : explicitPenalty*J*c*log 16 ≤
      explicitPenalty*(20371547/1000000000:ℝ)*(4/5)*(13863/5000) := by
    have hJC := mul_le_mul hJ hc hc0 (by norm_num : (0:ℝ)≤20371547/1000000000)
    have h1 := mul_le_mul hJC log_sixteen_upper hlog0 (by norm_num : (0:ℝ)≤(20371547/1000000000:ℝ)*(4/5))
    have h2 := mul_le_mul_of_nonneg_left h1 (by unfold explicitPenalty; norm_num : 0 ≤ explicitPenalty)
    nlinarith
  have hcapnum1 : 0 ≤ explicitPenalty*(20371547/1000000000:ℝ)*(4/5)*(13863/5000) := by norm_num [explicitPenalty]
  have hfrac1 : explicitPenalty*J*c*log 16/mvBlockDenom 16 42 ≤
      explicitPenalty*(20371547/1000000000:ℝ)*(4/5)*(13863/5000)/qlo :=
    (div_le_div_of_nonneg_right hnum1 hq0.le).trans
      (div_le_div_of_nonneg_left hcapnum1 hqlo hq)
  have hnum2 : 2*explicitPenalty*H ≤ 2*explicitPenalty*(57139/500000:ℝ) := by
    exact mul_le_mul_of_nonneg_left hH (by unfold explicitPenalty; norm_num)
  have hcapnum2 : 0 ≤ 2*explicitPenalty*(57139/500000:ℝ) := by norm_num [explicitPenalty]
  have hfrac2 : 2*explicitPenalty*H/(16*mvBlockDenom 16 42) ≤
      2*explicitPenalty*(57139/500000:ℝ)/(16*qlo) :=
    (div_le_div_of_nonneg_right hnum2 (by positivity : 0 ≤ (16:ℝ)*mvBlockDenom 16 42)).trans
      (div_le_div_of_nonneg_left hcapnum2 (by positivity : 0 < (16:ℝ)*qlo)
        (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤16)))
  have hcap : -(10509/10000:ℝ)+
      explicitPenalty*(20371547/1000000000:ℝ)*(4/5)*(13863/5000)/qlo+
      2*explicitPenalty*(57139/500000:ℝ)/(16*qlo)+(3/2500:ℝ) ≤ -(1939/2500:ℝ) := by
    norm_num [explicitPenalty,qlo]
  unfold explicitConstant
  linarith

theorem w4_constant_cap (c J H S : ℝ) (hH : H ≤ (14327/125000:ℝ))
    (hS : S ≤ -(26/25:ℝ)) : explicitConstant c J H S 1 ≤ 0 := by
  unfold explicitConstant mvBlockDenom
  norm_num
  unfold explicitPenalty
  nlinarith

#print axioms fap_signed_cap
#print axioms w4_signed_cap
#print axioms fap_constant_cap
#print axioms w4_constant_cap
end RH080Next.Explicit
