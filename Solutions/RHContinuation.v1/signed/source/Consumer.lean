/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Convergence
import FiniteCorrection
import AbelFinite
import Mathlib.Analysis.Complex.ExponentialBounds
namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set

theorem exp_six_gt_four_hundred : (400:ℝ) < Real.exp 6 := by
  have hp : (400:ℝ) < (Real.exp 1)^6 := by
    calc (400:ℝ) < (2.7182818283:ℝ)^6 := by norm_num
      _ < (Real.exp 1)^6 := by gcongr; exact Real.exp_one_gt_d9
  have he : (Real.exp 1)^6 = Real.exp 6 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rwa [he] at hp

theorem sqrt_exp_double (t : ℝ) : Real.sqrt (Real.exp (2*t)) = Real.exp t := by
  have he : Real.exp (2*t) = (Real.exp t)^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [he,Real.sqrt_sq_eq_abs,abs_of_pos (Real.exp_pos t)]

/-- ROOT_POST_LOCK_SYNTHESIS. The full requested closed band is covered. The only
unproved premises are explicitly named original-publication source predicates; no sign
assumption or new numeric provider is used. All finite prime-power, Abel and scalar
transport steps are proved above for the actual Mathlib functions. -/
theorem first_mertens_positive
    (hCA : PublishedBFKNW_CA_RH)
    (hPsi : PublishedButhePsi) (hThetaL : PublishedButheThetaLower)
    (hThetaU : PublishedButheThetaUpper) (hRH : RiemannHypothesis)
    {x : ℝ} (hx : Real.exp 24 ≤ x) (hxM : x ≤ (10:ℝ)^19) :
    0.006 / Real.sqrt x < A x - Real.log x - E := by
  let y := Real.sqrt x
  let z := Real.sqrt y
  let M : ℝ := (10:ℝ)^19
  have hx0 : 0 < x := (Real.exp_pos 24).trans_le hx
  have hy0 : 0 < y := Real.sqrt_pos.mpr hx0
  have hz0 : 0 < z := Real.sqrt_pos.mpr hy0
  have hy2 : y^2 = x := Real.sq_sqrt hx0.le
  have hz2 : z^2 = y := Real.sq_sqrt hy0.le
  have hy12 : Real.exp 12 ≤ y := by
    have h := Real.sqrt_le_sqrt hx
    simpa only [show (24:ℝ)=2*12 by norm_num,sqrt_exp_double] using h
  have hz6 : Real.exp 6 ≤ z := by
    have h := Real.sqrt_le_sqrt hy12
    simpa only [show (12:ℝ)=2*6 by norm_num,sqrt_exp_double] using h
  have hz400 : (400:ℝ) < z := exp_six_gt_four_hundred.trans_le hz6
  have hy160 : (160000:ℝ) < y := by nlinarith [sq_nonneg (z-400)]
  have hx11 : 11 < x := by nlinarith [sq_nonneg (y-160000)]
  have hyM : y ≤ M := by
    dsimp [M]
    nlinarith [sq_nonneg (y-1)]
  have hU : Chebyshev.theta y ≤ y-0.05*Real.sqrt y :=
    (hThetaU y (by linarith) hyM).le
  have hL : ∀ t ∈ Set.Ioc y M, t-1.95*Real.sqrt t ≤ Chebyshev.theta t := by
    intro t ht
    exact hThetaL t (by linarith [ht.1]) ht.2
  have hAbel := finite_square_lower hy0 hyM hU hL
  have hTail := fullTail_ge_squareFinite correction_summable (M := M) (by linarith : 2 ≤ x)
  have hT : 1/y - 2.55/(y*z) - 2/M ≤ fullTail x := hAbel.trans hTail
  have hy10 : y < (10000000000:ℝ) := by nlinarith
  have hratio : y/M < (0.000000001:ℝ) := by
    rw [div_lt_iff₀ (by dsimp [M]; positivity)]
    dsimp [M]
    norm_num
    exact hy10
  have hcoef : (2.55:ℝ)/z < 2.55/400 :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hz400
  have hTmul : (0.993624998:ℝ) < y*fullTail x := by
    have hm := mul_le_mul_of_nonneg_left hT hy0.le
    have he : y*(1/y-2.55/(y*z)-2/M) = 1-2.55/z-2*(y/M) := by
      field_simp [ne_of_gt hy0,ne_of_gt hz0] <;> ring
    rw [he] at hm
    linarith
  have hRes : (2:ℝ)/y < 1/80000 := by
    rw [div_lt_iff₀ hy0]
    linarith
  have hc := hCA hRH x (by linarith)
  have hb := hPsi x hx11 hxM
  have hc' : |CA x-Real.log x+Real.eulerMascheroniConstant| ≤
      0.94*y/x+0.0476/y+2/x := by
    exact hc.trans (by gcongr)
  have hcm := mul_le_mul_of_nonneg_left (abs_le.mp hc').1 hy0.le
  have hec : y * -(0.94*y/x+0.0476/y+2/x) = -(0.94+0.0476+2/y) := by
    rw [← hy2]
    field_simp [ne_of_gt hy0] <;> ring
  rw [hec] at hcm
  have hFinal : (0.006:ℝ) < (A x-Real.log x-E)*y := by
    rw [normalized_identity]
    nlinarith
  exact (div_lt_iff₀ hy0).mpr hFinal

#print axioms first_mertens_positive
end MertensPositive
