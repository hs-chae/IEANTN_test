import SynergyAnalytic.PrimeRich
namespace SynergyAnalytic
open Real Set MeasureTheory IEANTN
set_option maxHeartbeats 0

theorem prime_rich_width_parameter
    {A C x0 x : ℝ} (hA0:0 ≤ A) (hAmax:A ≤ 9/500) (hC : 0 ≤ C) (hp : HasPowerLogBound Eπ C 0 (7/8) x0)
    (hstart : x0 ≤ x) (hx : Real.exp 330 ≤ x) :
    (A/(1000001/1000000)-C*(5001/5000+1))*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+A*x^((7:ℝ)/8))-primeCounting x := by
  let y : ℝ := x+A*x^((7:ℝ)/8)
  let w : ℝ := x^((7:ℝ)/8)/Real.log x
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hxHuge := exp330_ge_power.trans hx
  have hx2 : 2 ≤ x := by norm_num at hxHuge;linarith
  have hx1 : 1 < x := by linarith
  have hlog : 330 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (330:ℝ)) hx
    simpa only [Real.log_exp] using hh
  have hlp : 0 < Real.log x := by linarith
  have hxy : x ≤ y := by dsimp [y];exact le_add_of_nonneg_right (mul_nonneg hA0 (Real.rpow_nonneg hx0.le ((7:ℝ)/8)))
  have hy0 : 0 < y := hx0.trans_le hxy
  have hyl : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hlyp : 0 < Real.log y := hlp.trans_le hyl
  have hwidth := short_width_fraction hx
  have hycap : y ≤ (5001/5000:ℝ)*x := by
    have hAw:=mul_le_mul_of_nonneg_right hAmax (Real.rpow_nonneg hx0.le ((7:ℝ)/8))
    dsimp [y]
    linarith
  have hlogcap : Real.log y ≤ (1000001/1000000:ℝ)*Real.log x := by
    have hh := Real.log_le_log hy0 hycap
    rw [Real.log_mul (by norm_num : (5001/5000:ℝ)≠0) hx0.ne'] at hh
    have hn := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<5001/5000)
    nlinarith
  have hypow : y^((7:ℝ)/8) ≤ (5001/5000:ℝ)*x^((7:ℝ)/8) := by
    have hr := Real.rpow_le_rpow hy0.le hycap (by norm_num : (0:ℝ)≤7/8)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤5001/5000) hx0.le] at hr
    have hc := Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ)≤5001/5000)
      (by norm_num : (7/8:ℝ)≤1)
    exact hr.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hx0.le _))
  have herror : y^((7:ℝ)/8)/Real.log y ≤ (5001/5000:ℝ)*w := by
    calc
      _ ≤ ((5001/5000:ℝ)*x^((7:ℝ)/8))/Real.log y :=
        div_le_div_of_nonneg_right hypow hlyp.le
      _ ≤ ((5001/5000:ℝ)*x^((7:ℝ)/8))/Real.log x :=
        div_le_div_of_nonneg_left (by positivity) hlp hyl
      _ = _ := by dsimp [w];ring
  have hmain : (A/(1000001/1000000))*w ≤ (y-x)/Real.log y := by
    have hh := div_le_div_of_nonneg_left
      (by positivity : (0:ℝ)≤A*x^((7:ℝ)/8)) hlyp hlogcap
    convert hh using 1 <;> first | rfl | (dsimp [w,y];field_simp <;> ring)
  have hr := prime_count_difference_lower hp hstart hx2 hxy
  have hw : 0 ≤ w := by dsimp [w];positivity
  have hm := mul_le_mul_of_nonneg_left herror hC
  change (A/(1000001/1000000)-C*(5001/5000+1))*x^((7:ℝ)/8)/Real.log x ≤ primeCounting y-primeCounting x
  have hwid : x^((7:ℝ)/8)/Real.log x = w := rfl
  rw [hwid] at hr
  rw [mul_div_assoc,hwid]
  nlinarith


theorem prime_rich_017_008442
    (hp:HasPowerLogBound Eπ (4221/500000) 0 (7/8) (Real.exp 330))
    {x:ℝ} (hx:Real.exp 330 ≤ x) :
    (57/500000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(17/1000:ℝ)*x^((7:ℝ)/8))-primeCounting x := by
  have hr:=prime_rich_width_parameter (A:=17/1000)
    (by norm_num) (by norm_num) (by norm_num : (0:ℝ) ≤ 4221/500000) hp hx hx
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  have hhuge:=exp330_ge_power.trans hx
  have hx1 : 1<x := by norm_num at hhuge;linarith
  have hl : 0<Real.log x := Real.log_pos hx1
  have hw : 0 ≤ x^((7:ℝ)/8)/Real.log x := by positivity
  have hc : (57/500000:ℝ) ≤ (17/1000)/(1000001/1000000)-(4221/500000)*(5001/5000+1) := by norm_num
  have hm:=mul_le_mul_of_nonneg_right hc hw
  simp only [←mul_div_assoc] at hm
  exact hm.trans hr

#print axioms prime_rich_width_parameter
#print axioms prime_rich_017_008442
end SynergyAnalytic
