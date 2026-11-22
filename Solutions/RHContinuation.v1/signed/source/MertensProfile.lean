/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTNAdapters
namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set

/-- The square-tail profile retains the actual BFKNW mass constant and the dependence
on x discarded by the previous .006 export. The finite endpoint remains explicit. -/
noncomputable def squareProfile (x : ℝ) : ℝ :=
  0.01379001 - 2.55 / Real.sqrt (Real.sqrt x) -
    2 * Real.sqrt x / (10:ℝ)^19 - 2 / Real.sqrt x

/-- Whole-real, same-original-premise profile. It proves a mathematical lower function,
not an assumed sign provider or a numerical sample. -/
theorem first_mertens_square_profile
    (h154 : SourceBFKNW154) (h21 : SourceBFKNW21)
    (hPsi : PublishedButhePsi) (hThetaL : PublishedButheThetaLower)
    (hThetaU : PublishedButheThetaUpper) (hRH : RiemannHypothesis)
    {x : ℝ} (hx : (1423:ℝ)^2 ≤ x) (hxM : x ≤ (10:ℝ)^19) :
    squareProfile x ≤ Real.sqrt x * (A x - Real.log x - E) := by
  let y := Real.sqrt x
  let z := Real.sqrt y
  let M : ℝ := (10:ℝ)^19
  have hx0 : 0 < x := by nlinarith
  have hy0 : 0 < y := Real.sqrt_pos.mpr hx0
  have hz0 : 0 < z := Real.sqrt_pos.mpr hy0
  have hy2 : y^2 = x := Real.sq_sqrt hx0.le
  have hy1423 : (1423:ℝ) ≤ y := by
    exact (Real.le_sqrt (by norm_num) hx0.le).mpr hx
  have hyM : y ≤ M := by
    dsimp [M]
    nlinarith [sq_nonneg (y-1)]
  have hU : Chebyshev.theta y ≤ y-0.05*Real.sqrt y :=
    (hThetaU y (by linarith) hyM).le
  have hL : ∀ t ∈ Set.Ioc y M, t-1.95*Real.sqrt t ≤ Chebyshev.theta t := by
    intro t ht
    exact hThetaL t (by linarith [ht.1]) ht.2
  have hAbel := finite_square_lower hy0 hyM hU hL
  have hTail := fullTail_ge_squareFinite correction_summable (M := M)
    (by nlinarith : 2 ≤ x)
  have hT : 1/y - 2.55/(y*z) - 2/M ≤ fullTail x := hAbel.trans hTail
  have hm := mul_le_mul_of_nonneg_left hT hy0.le
  have he : y*(1/y-2.55/(y*z)-2/M) = 1-2.55/z-2*y/M := by
    field_simp [ne_of_gt hy0,ne_of_gt hz0] <;> ring
  rw [he] at hm
  have hc := h154 x (by nlinarith)
  rw [J1_eq_mass_div_sqrt hRH hx0] at hc
  have hJ : reciprocalMass / y ≤ 0.04620999 / y :=
    div_le_div_of_nonneg_right h21.2 hy0.le
  have hc2 : |CA x-Real.log x+Real.eulerMascheroniConstant| ≤
      0.94*y/x + 0.04620999/y + 2/x := by
    have hp := hPsi x (by nlinarith) hxM
    have hpd := div_le_div_of_nonneg_right hp hx0.le
    have hlog := div_le_div_of_nonneg_right log_two_pi_lt_two.le hx0.le
    linarith
  have hcm := mul_le_mul_of_nonneg_left (abs_le.mp hc2).1 hy0.le
  have hec : y * -(0.94*y/x+0.04620999/y+2/x) =
      -(0.94+0.04620999+2/y) := by
    rw [← hy2]
    field_simp [ne_of_gt hy0] <;> ring
  rw [hec] at hcm
  rw [normalized_identity]
  dsimp [squareProfile, y, z, M] at hm hcm ⊢
  nlinarith

/-- Earlier finite band: no source hypotheses are added. -/
theorem first_mertens_positive_earlier
    (h154 : SourceBFKNW154) (h21 : SourceBFKNW21)
    (hPsi : PublishedButhePsi) (hThetaL : PublishedButheThetaLower)
    (hThetaU : PublishedButheThetaUpper) (hRH : RiemannHypothesis)
    {x : ℝ} (hx : Real.exp 21 ≤ x) (hxM : x ≤ (10:ℝ)^19) :
    0.00031 / Real.sqrt x < A x - Real.log x - E := by
  have he : (190:ℝ)^4 < Real.exp 21 := by
    calc (190:ℝ)^4 < (2.7182818283:ℝ)^21 := by norm_num
      _ < (Real.exp 1)^21 := by gcongr; exact Real.exp_one_gt_d9
      _ = Real.exp 21 := by rw [← Real.exp_nat_mul]; norm_num
  have hx0 : 0 < x := (Real.exp_pos 21).trans_le hx
  have hy0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hz190 : (190:ℝ) < Real.sqrt (Real.sqrt x) := by
    apply Real.lt_sqrt_of_sq_lt
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [he.trans_le hx]
  have hy36100 : (36100:ℝ) < Real.sqrt x := by
    have h := (Real.lt_sqrt (by norm_num)).mp hz190
    norm_num at h
    exact h
  have hy10 : Real.sqrt x < (10000000000:ℝ) := by
    apply (Real.sqrt_lt hx0.le (by norm_num)).mpr
    nlinarith
  have hratio : 2*Real.sqrt x/(10:ℝ)^19 < 0.000000002 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hc1 : 2.55 / Real.sqrt (Real.sqrt x) < 2.55/(190:ℝ) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hz190
  have hc2 : 2 / Real.sqrt x < 2/(36100:ℝ) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hy36100
  have hmin : (0.00031:ℝ) < squareProfile x := by
    dsimp [squareProfile]
    linarith
  have hp := first_mertens_square_profile h154 h21 hPsi hThetaL hThetaU hRH
    (x := x) (by nlinarith) hxM
  apply (div_lt_iff₀ hy0).mpr
  nlinarith

/-- Improved margin on the complete old band. -/
theorem first_mertens_positive_stronger
    (h154 : SourceBFKNW154) (h21 : SourceBFKNW21)
    (hPsi : PublishedButhePsi) (hThetaL : PublishedButheThetaLower)
    (hThetaU : PublishedButheThetaUpper) (hRH : RiemannHypothesis)
    {x : ℝ} (hx : Real.exp 24 ≤ x) (hxM : x ≤ (10:ℝ)^19) :
    0.00745 / Real.sqrt x < A x - Real.log x - E := by
  have he : (403:ℝ)^4 < Real.exp 24 := by
    calc (403:ℝ)^4 < (2.7182818283:ℝ)^24 := by norm_num
      _ < (Real.exp 1)^24 := by gcongr; exact Real.exp_one_gt_d9
      _ = Real.exp 24 := by rw [← Real.exp_nat_mul]; norm_num
  have hx0 : 0 < x := (Real.exp_pos 24).trans_le hx
  have hy0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hz403 : (403:ℝ) < Real.sqrt (Real.sqrt x) := by
    apply Real.lt_sqrt_of_sq_lt
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [he.trans_le hx]
  have hy162409 : (162409:ℝ) < Real.sqrt x := by
    have h := (Real.lt_sqrt (by norm_num)).mp hz403
    norm_num at h
    exact h
  have hy10 : Real.sqrt x < (10000000000:ℝ) := by
    apply (Real.sqrt_lt hx0.le (by norm_num)).mpr
    nlinarith
  have hratio : 2*Real.sqrt x/(10:ℝ)^19 < 0.000000002 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hc1 : 2.55 / Real.sqrt (Real.sqrt x) < 2.55/(403:ℝ) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hz403
  have hc2 : 2 / Real.sqrt x < 2/(162409:ℝ) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hy162409
  have hmin : (0.00745:ℝ) < squareProfile x := by
    dsimp [squareProfile]
    linarith
  have hp := first_mertens_square_profile h154 h21 hPsi hThetaL hThetaU hRH
    (x := x) (by nlinarith) hxM
  apply (div_lt_iff₀ hy0).mpr
  nlinarith

#print axioms first_mertens_square_profile
#print axioms first_mertens_positive_earlier
#print axioms first_mertens_positive_stronger
end MertensPositive
