import WinnerDensityA.PiecewiseMoment
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerDensityA.Piecewise CH2QRH
set_option maxHeartbeats 0

/-- Uniform exponential-affine upper bound for the entire power/log tail
above exp60. It uses four ordinary integrations by parts; no numerical
quadrature or unverified tail assumption. -/
theorem tail_four_upper_affine {sigma : ℝ}
    (hs : (3/4:ℝ)≤sigma) (hs' : sigma≤7/8) :
    upper (8*(1-sigma)/3) 4 (Real.exp 60) ≤
      (1/1000000000:ℝ)*Real.exp (160*((7/8)-sigma)) := by
  let p := 8*(1-sigma)/3
  let r := 1-p
  have hr : (1/3:ℝ)≤r := by dsimp [r,p];linarith
  have hrp : 0<r := by linarith
  have hpoly : (60:ℝ)^4/r*(1+4/(r*60)+12/(r*60)^2+24/(r*60)^3+24/(r*60)^4) ≤ 47944872 := by
    calc
      _ ≤ (60:ℝ)^4/(1/3)*(1+4/((1/3)*60)+12/((1/3)*60)^2+24/((1/3)*60)^3+24/((1/3)*60)^4) := by gcongr
      _ = 47944872 := by norm_num
  have hu : upper p 4 (Real.exp 60) =
      Real.exp (60*(p-1))*((60:ℝ)^4/r*(1+4/(r*60)+12/(r*60)^2+24/(r*60)^3+24/(r*60)^4)) := by
    unfold upper
    rw [Real.rpow_def_of_pos (Real.exp_pos 60),Real.log_exp]
    norm_num [Real.log_exp,Real.rpow_ofNat]
    dsimp [r]
    ring
  have he40 : (8/3:ℝ)^40≤Real.exp 40 := by
    calc
      _ ≤ (Real.exp 1)^40 := pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.exp_one_gt_d9]) 40
      _ = Real.exp 40 := by rw [←Real.exp_nat_mul];norm_num
  have hw : (47944872:ℝ)*Real.exp (-40)≤1/1000000000 := by
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos 40)).mpr
    exact (by norm_num : (47944872:ℝ)≤(1/1000000000)*(8/3:ℝ)^40).trans
      (mul_le_mul_of_nonneg_left he40 (by norm_num))
  rw [hu]
  have hh := mul_le_mul_of_nonneg_left hpoly (Real.exp_pos (60*(p-1))).le
  apply hh.trans
  rw [show 60*(p-1)= -40+160*((7/8)-sigma) by dsimp [p];ring,Real.exp_add]
  have hm := mul_le_mul_of_nonneg_right hw (Real.exp_pos (160*((7/8)-sigma))).le
  nlinarith

/-- A finite tail bound sufficient for the finite partial-summation limit. -/
theorem tail_integral_four_affine {sigma T K : ℝ}
    (hs : (3/4:ℝ)≤sigma) (hs' : sigma≤7/8) (hT : Real.exp 60≤T) (hK : 0≤K) :
    (∫u in Real.exp 60..T,K*u^(8*(1-sigma)/3)*Real.log u^(5-2*sigma)/u^2) ≤
      (K/1000000000)*Real.exp (160*((7/8)-sigma)) := by
  have hA : 1<Real.exp (60:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have hp : 0≤8*(1-sigma)/3 := by linarith
  have hp1 : 8*(1-sigma)/3<1 := by linarith
  have hq : 5-2*sigma≤4 := by linarith
  have hi := power_log_intervalIntegrable (p:=8*(1-sigma)/3) (q:=5-2*sigma) hA hT
  have hi4 := power_log_intervalIntegrable (p:=8*(1-sigma)/3) (q:=4) hA hT
  have hm := intervalIntegral.integral_mono_on hT hi hi4 (fun u hu => by
    have hu1 : 1≤Real.log u := by
      have hh := Real.log_le_log (Real.exp_pos 60) hu.1
      rw [Real.log_exp] at hh
      linarith
    have hu0 : 0<u := (Real.exp_pos 60).trans_le hu.1
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hu1 hq) (by positivity)) (sq_nonneg u))
  have ht0 : 0<T := (Real.exp_pos 60).trans_le hT
  have hlt : 0<Real.log T := Real.log_pos (hA.trans_le hT)
  have hfour := power_log_tail_four (q:=4) hA hT hp hp1 (by norm_num) le_rfl
  have hnon : 0≤T^(8*(1-sigma)/3)*Real.log T^(4:ℝ)/T := by positivity
  have hbound := hm.trans ((le_add_of_nonneg_left hnon).trans hfour)
  have hfinal := hbound.trans (tail_four_upper_affine hs hs')
  have hmul := mul_le_mul_of_nonneg_left hfinal hK
  rw [←intervalIntegral.integral_const_mul] at hmul
  convert hmul using 1 <;> first | rfl | ring

#print axioms tail_four_upper_affine
#print axioms tail_integral_four_affine
end SynergyAnalytic
