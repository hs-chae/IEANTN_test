import IEANTN.Vocabulary.PowerError
import Mathlib

namespace SynergyAnalytic
open Real Set MeasureTheory IEANTN
set_option maxHeartbeats 0

theorem invLog_continuousOn : ContinuousOn (fun t : ℝ => 1/Real.log t) (Ici 2) := by
  intro t ht
  have ht1 : 1 < t := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) ht
  have ht0 : 0 < t := by linarith
  exact (continuousAt_const.div (Real.continuousAt_log ht0.ne') (Real.log_pos ht1).ne').continuousWithinAt

theorem Li_interval_lower {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    (y-x)/Real.log y ≤ Li y-Li x := by
  have hy : 2 ≤ y := hx.trans hxy
  have hi2x : IntervalIntegrable (fun t : ℝ => 1/Real.log t) volume 2 x :=
    (invLog_continuousOn.mono (by
      rw [uIcc_of_le hx];intro t ht;exact ht.1)).intervalIntegrable
  have hixy : IntervalIntegrable (fun t : ℝ => 1/Real.log t) volume x y :=
    (invLog_continuousOn.mono (by
      rw [uIcc_of_le hxy];intro t ht;exact hx.trans ht.1)).intervalIntegrable
  have hd : Li y-Li x = ∫ t in x..y, 1/Real.log t := by
    have hh := intervalIntegral.integral_add_adjacent_intervals hi2x hixy
    unfold Li
    linarith
  rw [hd]
  have hm : (∫ t in x..y, 1/Real.log y) ≤ ∫ t in x..y, 1/Real.log t := by
    apply intervalIntegral.integral_mono_on hxy intervalIntegrable_const hixy
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact one_div_le_one_div_of_le (Real.log_pos ht1)
      (Real.log_le_log (by linarith : 0<t) ht.2)
  simpa [intervalIntegral.integral_const,smul_eq_mul,div_eq_mul_inv] using hm

theorem raw_pi_error_of_power_bound
    {C x x0 : ℝ} (hp : HasPowerLogBound Eπ C 0 (7/8) x0)
    (hx : x0 ≤ x) (hx1 : 1 < x) :
    |primeCounting x-Li x| ≤ C*x^((7:ℝ)/8)/Real.log x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hb := hp x hx
  simp only [pow_zero,mul_one,Eπ] at hb
  have hb' := (div_le_iff₀ (div_pos hx0 hl)).mp hb
  have he : x^((7/8:ℝ)-1)*x = x^((7:ℝ)/8) := by
    calc
      _ = x^((7/8:ℝ)-1)*x^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hx0];norm_num
  convert hb' using 1 <;> first | rfl | (rw [← he];ring)

theorem prime_count_difference_lower
    {C x0 x y : ℝ} (hp : HasPowerLogBound Eπ C 0 (7/8) x0)
    (hx0 : x0 ≤ x) (hx : 2 ≤ x) (hxy : x ≤ y) :
    (y-x)/Real.log y-C*(y^((7:ℝ)/8)/Real.log y+x^((7:ℝ)/8)/Real.log x) ≤
      primeCounting y-primeCounting x := by
  have heX := raw_pi_error_of_power_bound hp hx0 (by linarith)
  have heY := raw_pi_error_of_power_bound hp (hx0.trans hxy) (by linarith)
  have hi := Li_interval_lower hx hxy
  have hX := (abs_le.mp heX).2
  have hY := (abs_le.mp heY).1
  simp only [mul_div_assoc] at hX hY
  nlinarith

theorem exp330_ge_power : (100:ℝ)^8 ≤ Real.exp 330 := by
  have he : (31:ℝ) ≤ Real.exp 30 := by linarith [Real.add_one_le_exp (30:ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤31) he 11
  have hexp : (Real.exp 30)^11 = Real.exp 330 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hexp] at hp
  norm_num at hp ⊢
  linarith

theorem short_width_fraction {x : ℝ} (hx : Real.exp 330 ≤ x) :
    x^((7:ℝ)/8) ≤ x/100 := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hhuge : (100:ℝ)^8 ≤ x := exp330_ge_power.trans hx
  have hs := Real.rpow_le_rpow (by positivity : (0:ℝ)≤100^8) hhuge
    (by norm_num : (0:ℝ)≤1/8)
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤100) 8 (1/8)] at hs
  norm_num at hs
  have he : x^((7:ℝ)/8)*x^((1:ℝ)/8) = x := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hx0.le ((7:ℝ)/8))
  rw [he] at hm
  linarith

/-- A prime-rich interval conclusion, rather than only existence of one prime.
The source error is normalized by x/log x and Li is the integral from 2. -/
theorem prime_rich_parameter
    {C x0 x : ℝ} (hC : 0 ≤ C) (hp : HasPowerLogBound Eπ C 0 (7/8) x0)
    (hstart : x0 ≤ x) (hx : Real.exp 330 ≤ x) :
    ((9/500:ℝ)/(1000001/1000000)-C*(5001/5000+1))*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(9/500:ℝ)*x^((7:ℝ)/8))-primeCounting x := by
  let y : ℝ := x+(9/500:ℝ)*x^((7:ℝ)/8)
  let w : ℝ := x^((7:ℝ)/8)/Real.log x
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hxHuge := exp330_ge_power.trans hx
  have hx2 : 2 ≤ x := by norm_num at hxHuge;linarith
  have hx1 : 1 < x := by linarith
  have hlog : 330 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (330:ℝ)) hx
    simpa only [Real.log_exp] using hh
  have hlp : 0 < Real.log x := by linarith
  have hxy : x ≤ y := by dsimp [y];nlinarith [Real.rpow_nonneg hx0.le ((7:ℝ)/8)]
  have hy0 : 0 < y := hx0.trans_le hxy
  have hyl : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hlyp : 0 < Real.log y := hlp.trans_le hyl
  have hwidth := short_width_fraction hx
  have hycap : y ≤ (5001/5000:ℝ)*x := by dsimp [y];linarith
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
  have hmain : ((9/500:ℝ)/(1000001/1000000))*w ≤ (y-x)/Real.log y := by
    have hh := div_le_div_of_nonneg_left
      (by positivity : (0:ℝ)≤(9/500:ℝ)*x^((7:ℝ)/8)) hlyp hlogcap
    convert hh using 1 <;> first | rfl | (dsimp [w,y];field_simp <;> ring)
  have hr := prime_count_difference_lower hp hstart hx2 hxy
  have hw : 0 ≤ w := by dsimp [w];positivity
  have hm := mul_le_mul_of_nonneg_left herror hC
  change ((9/500:ℝ)/(1000001/1000000)-C*(5001/5000+1))*x^((7:ℝ)/8)/Real.log x ≤ primeCounting y-primeCounting x
  have hwid : x^((7:ℝ)/8)/Real.log x = w := rfl
  rw [hwid] at hr
  rw [mul_div_assoc,hwid]
  nlinarith

 theorem prime_rich_0086
    (hp : HasPowerLogBound Eπ (43/5000) 0 (7/8) (Real.exp 330))
    {x : ℝ} (hx : Real.exp 330 ≤ x) :
    (79/100000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(9/500:ℝ)*x^((7:ℝ)/8))-primeCounting x := by
  have hr := prime_rich_parameter (by norm_num : (0:ℝ)≤43/5000) hp hx hx
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hx1 : 1 < x := by
    have hh := exp330_ge_power.trans hx
    norm_num at hh
    linarith
  have hlp : 0 < Real.log x := Real.log_pos hx1
  have hw : 0 ≤ x^((7:ℝ)/8)/Real.log x := by positivity
  have hc : (79/100000:ℝ) ≤ (9/500)/(1000001/1000000)-(43/5000)*(5001/5000+1) := by norm_num
  have hm := mul_le_mul_of_nonneg_right hc hw
  simp only [← mul_div_assoc] at hm
  exact hm.trans hr

 theorem prime_rich_profile
    (C : ℝ → ℝ) (hC : ∀ L ≥ 330, 0 ≤ C L) (hanti : AntitoneOn C (Ici 330))
    (hp : ∀ z ≥ Real.exp 330, Eπ z ≤ C (Real.log z)*z^((7/8:ℝ)-1))
    {x : ℝ} (hx : Real.exp 330 ≤ x) :
    ((9/500:ℝ)/(1000001/1000000)-C (Real.log x)*(5001/5000+1))*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(9/500:ℝ)*x^((7:ℝ)/8))-primeCounting x := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hlog : 330 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (330:ℝ)) hx
    simpa only [Real.log_exp] using hh
  have hlocal : HasPowerLogBound Eπ (C (Real.log x)) 0 (7/8) x := by
    intro z hz
    have hlogz : Real.log x ≤ Real.log z := Real.log_le_log hx0 hz
    have hc := hanti hlog (hlog.trans hlogz) hlogz
    have hr := (hp z (hx.trans hz)).trans
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (hx0.le.trans hz) _))
    simpa only [pow_zero,mul_one] using hr
  exact prime_rich_parameter (hC _ hlog) hlocal le_rfl hx

#print axioms prime_rich_0086
#print axioms prime_rich_profile
end SynergyAnalytic
