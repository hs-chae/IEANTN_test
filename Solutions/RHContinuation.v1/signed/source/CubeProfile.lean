/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CubeAbel
namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set

noncomputable def cubeGain (u : ℝ) : ℝ :=
  0.5/u^2 - 2.55/u^3 - 2.29/u^4 - 2.5/u^6

/-- Recovered omitted cubes give a new lower profile for the actual prime sum,
using exactly the old five published predicates and RH. -/
theorem first_mertens_cube_profile_u
    (h154 : SourceBFKNW154) (h21 : SourceBFKNW21)
    (hPsi : PublishedButhePsi) (hThetaL : PublishedButheThetaLower)
    (hThetaU : PublishedButheThetaUpper) (hRH : RiemannHypothesis)
    {u : ℝ} (hu : 7 ≤ u) (hM : u^12 ≤ (10:ℝ)^19) :
    0.01379001 + cubeGain u - 2*u^6/(10:ℝ)^19 ≤
      u^6 * (A (u^12) - Real.log (u^12) - E) := by
  let x := u^12
  let y := u^6
  let z := u^3
  let w := u^4
  let M : ℝ := (10:ℝ)^19
  have hu0 : 0 < u := by linarith
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hw0 : 0 < w := by dsimp [w]; positivity
  have hysq : y^2=x := by dsimp [x,y]; ring
  have hy : Real.sqrt x=y := by
    rw [← hysq,Real.sqrt_sq_eq_abs,abs_of_pos hy0]
  have hz : Real.sqrt y=z := by
    rw [show y=z^2 by dsimp [y,z]; ring,Real.sqrt_sq_eq_abs,abs_of_pos hz0]
  have hw : Real.sqrt w=u^2 := by
    rw [show w=(u^2)^2 by dsimp [w]; ring,Real.sqrt_sq_eq_abs,abs_of_nonneg (sq_nonneg u)]
  have hw3 : w^3=x := by dsimp [w,x]; ring
  have hw1423 : (1423:ℝ) ≤ w := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7) hu 4
    norm_num at hh
    dsimp [w]
    linarith
  have hwy : w ≤ y := by
    dsimp [w,y]
    exact pow_le_pow_right₀ (by linarith : 1 ≤ u) (by norm_num : (4:ℕ)≤6)
  have hyM : y ≤ M := by
    dsimp [M]
    nlinarith [sq_nonneg (y-1)]
  have hwM : w ≤ M := hwy.trans hyM
  have hU := (hThetaU y (by linarith) hyM).le
  have hL : ∀ t ∈ Set.Ioc y M, t-1.95*Real.sqrt t ≤ Chebyshev.theta t := by
    intro t ht
    exact hThetaL t (by linarith [ht.1]) ht.2
  have hAbelS := finite_square_lower hy0 hyM hU hL
  rw [hz] at hAbelS
  have hAbelC := finite_cube_lower hw0 hwy
    (hThetaU w (by linarith) hwM).le
    (hThetaL y (by linarith) hyM) (by
      intro t ht
      exact hThetaL t (by linarith [ht.1]) (ht.2.trans hyM))
  rw [hw] at hAbelC
  have hTail := fullTail_ge_square_add_cubeFinite (x:=x) (M:=M)
    (w:=w) (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7) hu 12])
    hw0.le hw3
  rw [hy] at hTail
  have hTotal : 1/y-2.55/(y*z)-2/M +
      (0.5/w^2-2.29/(w^2*u^2)-0.5/y^2) ≤ fullTail x := by
    exact (add_le_add hAbelS hAbelC).trans hTail
  have hm := mul_le_mul_of_nonneg_left hTotal hy0.le
  have he : y*(1/y-2.55/(y*z)-2/M+
      (0.5/w^2-2.29/(w^2*u^2)-0.5/y^2)) =
      1-2.55/u^3-2*u^6/M+0.5/u^2-2.29/u^4-0.5/u^6 := by
    dsimp [y,z,w]
    field_simp [ne_of_gt hu0] <;> ring
  rw [he] at hm
  have hc := h154 x (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7) hu 12])
  rw [J1_eq_mass_div_sqrt hRH hx0,hy] at hc
  have hJ : reciprocalMass/y ≤ 0.04620999/y :=
    div_le_div_of_nonneg_right h21.2 hy0.le
  have hc2 : |CA x-Real.log x+Real.eulerMascheroniConstant| ≤
      0.94*y/x+0.04620999/y+2/x := by
    have hp := hPsi x (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7) hu 12]) hM
    rw [hy] at hp
    have hpd := div_le_div_of_nonneg_right hp hx0.le
    have hlog := div_le_div_of_nonneg_right log_two_pi_lt_two.le hx0.le
    linarith
  have hcm := mul_le_mul_of_nonneg_left (abs_le.mp hc2).1 hy0.le
  have hec : y * -(0.94*y/x+0.04620999/y+2/x) =
      -(0.94+0.04620999+2/y) := by
    rw [← hysq]
    field_simp [ne_of_gt hy0] <;> ring
  rw [hec] at hcm
  change 0.01379001+cubeGain u-2*u^6/M ≤ y*(A x-Real.log x-E)
  rw [normalized_identity]
  dsimp only [cubeGain,y] at hm hcm ⊢
  convert (add_le_add hm hcm) using 1 <;> first | rfl | ring

/-- Simple exact rational interval bounds; three ranges cover the complete u interval. -/
theorem cube_gain_lower_on_segment {u a b : ℝ} (ha : 0 < a) (haU : a ≤ u)
    (huB : u ≤ b) (hcoef : 0 ≤ 0.5-2.55/a-2.29/a^2-2.5/a^4) :
    (0.5-2.55/a-2.29/a^2-2.5/a^4)/b^2 ≤ cubeGain u := by
  have hu : 0 < u := ha.trans_le haU
  have hb : 0 < b := hu.trans_le huB
  have ha2 := pow_le_pow_left₀ ha.le haU 2
  have ha4 := pow_le_pow_left₀ ha.le haU 4
  have hu2 := pow_le_pow_left₀ hu.le huB 2
  have hd1 : 2.55/u ≤ 2.55/a := div_le_div_of_nonneg_left (by norm_num) ha haU
  have hd2 : 2.29/u^2 ≤ 2.29/a^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) ha2
  have hd3 : 2.5/u^4 ≤ 2.5/a^4 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) ha4
  have hn : 0.5-2.55/a-2.29/a^2-2.5/a^4 ≤ 0.5-2.55/u-2.29/u^2-2.5/u^4 := by
    linarith
  have he : cubeGain u=(0.5-2.55/u-2.29/u^2-2.5/u^4)/u^2 := by
    dsimp [cubeGain]
    field_simp [ne_of_gt hu] <;> ring
  rw [he]
  exact (div_le_div_of_nonneg_left hcoef (by positivity) hu2).trans
    (div_le_div_of_nonneg_right hn (sq_nonneg u))

theorem cube_gain_lower {u : ℝ} (hu : 7 ≤ u) (hU : u ≤ 40) :
    (0.000229:ℝ) ≤ cubeGain u := by
  by_cases h10 : u ≤ 10
  · have h := cube_gain_lower_on_segment (a:=7) (b:=10) (by norm_num) hu h10 (by norm_num)
    norm_num at h
    linarith
  · by_cases h20 : u ≤ 20
    · have h := cube_gain_lower_on_segment (a:=10) (b:=20) (by norm_num)
        (by linarith) h20 (by norm_num)
      norm_num at h
      linarith
    · have h := cube_gain_lower_on_segment (a:=20) (b:=40) (by norm_num)
        (by linarith) hU (by norm_num)
      norm_num at h
      linarith

/-- The new cube-tail consumer more than doubles the old constant .006, on the
same entire real band and with the identical original publication/RH premises. -/
theorem first_mertens_positive_cube
    (h154 : SourceBFKNW154) (h21 : SourceBFKNW21)
    (hPsi : PublishedButhePsi) (hThetaL : PublishedButheThetaLower)
    (hThetaU : PublishedButheThetaUpper) (hRH : RiemannHypothesis)
    {x : ℝ} (hx : Real.exp 24 ≤ x) (hxM : x ≤ (10:ℝ)^19) :
    0.014 / Real.sqrt x < A x - Real.log x - E := by
  have hx0 : 0 < x := (Real.exp_pos 24).trans_le hx
  let u := Real.exp (Real.log x/12)
  have hu0 : 0 < u := Real.exp_pos _
  have hu12 : u^12=x := by
    dsimp [u]
    rw [← Real.exp_nat_mul]
    convert Real.exp_log hx0 using 1 <;> congr 1 <;> ring
  have hu : 7 ≤ u := by
    have hlog : (24:ℝ) ≤ Real.log x := by
      rwa [Real.le_log_iff_exp_le hx0]
    have hexp : Real.exp 2 ≤ u := Real.exp_le_exp.mpr (by linarith)
    have h7 : (7:ℝ) < Real.exp 2 := by
      calc (7:ℝ) < (2.7182818283:ℝ)^2 := by norm_num
        _ < (Real.exp 1)^2 := by gcongr; exact Real.exp_one_gt_d9
        _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    linarith
  have h40 : u < 40 := by
    apply lt_of_pow_lt_pow_left₀ 12 (by norm_num)
    rw [hu12]
    calc x ≤ (10:ℝ)^19 := hxM
      _ < (40:ℝ)^12 := by norm_num
  have hprofile := first_mertens_cube_profile_u h154 h21 hPsi hThetaL hThetaU hRH
    hu (hu12 ▸ hxM)
  have hgain := cube_gain_lower hu h40.le
  have hu6 : u^6=Real.sqrt x := by
    rw [← hu12,show (u^12)=(u^6)^2 by ring,Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0<u^6)]
  have hsqrt : Real.sqrt x < (10000000000:ℝ) := by
    apply (Real.sqrt_lt hx0.le (by norm_num)).mpr
    nlinarith
  have hend : 2*u^6/(10:ℝ)^19 < 0.000000002 := by
    rw [hu6,div_lt_iff₀ (by positivity)]
    nlinarith
  rw [hu12,hu6] at hprofile
  apply (div_lt_iff₀ (Real.sqrt_pos.mpr hx0)).mpr
  nlinarith

/-- Actual IEANTN Buthe conclusions are consumed, not reconstructed numerical inputs. -/
theorem first_mertens_positive_cube_IEANTN
    (h154 : SourceBFKNW154) (h21 : SourceBFKNW21)
    (hPsi : Buthe.v1.theorem_2_psi) (hThetaL : Buthe.v1.theorem_2_theta)
    (hThetaU : Buthe.v1.theorem_2_theta_lower) (hRH : RiemannHypothesis)
    {x : ℝ} (hx : Real.exp 24 ≤ x) (hxM : x ≤ (10:ℝ)^19) :
    0.014 / Real.sqrt x < A x - Real.log x - E :=
  first_mertens_positive_cube h154 h21 (buthe_psi_adapter hPsi)
    (buthe_theta_lower_adapter hThetaL) (buthe_theta_upper_adapter hThetaU) hRH hx hxM

#print axioms first_mertens_cube_profile_u
#print axioms cube_gain_lower
#print axioms first_mertens_positive_cube_IEANTN
end MertensPositive
