/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.HighIntegral
namespace E1NPlus
open Real Set MeasureTheory
set_option maxHeartbeats 0

theorem correction330_eq (s:ℝ) :
    correctionRay s 330=(12*330*((ulog 330)^2+2*ulog 330+2)*exp (-(330/8:ℝ)))*
      exp (-330*bandDelta s) := by
  have hu:ulog 330≠0:=(show 0<ulog 330 by linarith [u330_bounds.1]).ne'
  unfold correctionRay E1FrozenN.Interval.factor2
  rw [show -(1-s)*330=-(330/8:ℝ)+(-330*bandDelta s) by unfold bandDelta;ring,exp_add]
  field_simp [hu]
  <;> ring

theorem correction330_integrable {l r:ℝ} :
    IntervalIntegrable (fun s:ℝ↦correctionRay s 330) volume l r := by
  apply Continuous.intervalIntegrable
  unfold correctionRay
  fun_prop

theorem correction330_integral_upper :
    (∫s in (3/4:ℝ)..(7/8:ℝ),correctionRay s 330)<(1/10^12:ℝ) := by
  have hu:0<ulog 330:=by linarith [u330_bounds.1]
  have heq:(fun s:ℝ↦correctionRay s 330)=fun s↦
      (12*330*((ulog 330)^2+2*ulog 330+2)*exp (-(330/8:ℝ)))*exp (-330*bandDelta s) := by
    funext s
    exact correction330_eq s
  rw [heq,intervalIntegral.integral_const_mul,exp_band_integral (by norm_num : (330:ℝ)≠0)]
  have h0:bandDelta (7/8)=0:=by norm_num [bandDelta]
  have h1:-330*bandDelta (3/4)=-(330/8:ℝ):=by unfold bandDelta;ring
  rw [h0,mul_zero,exp_zero,h1]
  have hc:0 ≤ 12*((ulog 330)^2+2*ulog 330+2)*exp (-(330/8:ℝ)):=by positivity
  have hremove:12*330*((ulog 330)^2+2*ulog 330+2)*exp (-(330/8:ℝ))*
      ((1-exp (-(330/8:ℝ)))/330) ≤ 12*((ulog 330)^2+2*ulog 330+2)*exp (-(330/8:ℝ)) := by
    have hh:=mul_le_mul_of_nonneg_left (show 1-exp (-(330/8:ℝ)) ≤ 1 by linarith [exp_pos (-(330/8:ℝ))]) hc
    nlinarith only [hh]
  have he40:(10:ℝ)^17 ≤ exp 40 := by
    have hh:=(CH2Section7A.exp_nat_bounds 40).1
    norm_num at hh ⊢
    linarith
  have hex:(10:ℝ)^17 ≤ exp (330/8:ℝ):=he40.trans (exp_le_exp.mpr (by norm_num))
  have hinv:exp (-(330/8:ℝ)) ≤ (1/(10:ℝ)^17) := by
    rw [exp_neg,←one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hex
  have hup:(ulog 330)^2+2*ulog 330+2 ≤ (1403/20:ℝ)^2+2*(1403/20)+2 := by
    have hh:=pow_le_pow_left₀ hu.le u330_bounds.2 2
    nlinarith [u330_bounds.2]
  have hh:12*((ulog 330)^2+2*ulog 330+2)*exp (-(330/8:ℝ)) ≤
      12*((1403/20:ℝ)^2+2*(1403/20)+2)*(1/(10:ℝ)^17) := by gcongr
  exact hremove.trans_lt (hh.trans_lt (by norm_num))

theorem high330_le : high 330 ≤ (997/1000:ℝ) := by
  have heq:high 330=(∫s in (3/4:ℝ)..(7/8:ℝ),mainRay s 330)+
      (∫s in (3/4:ℝ)..(7/8:ℝ),correctionRay s 330) := by
    rw [high_as_integral]
    calc
      _ = ∫s in (3/4:ℝ)..(7/8:ℝ),mainRay s 330+correctionRay s 330 := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by norm_num : (3/4:ℝ) ≤ 7/8)] at hs
        exact integrand_eq s 330 hs (by norm_num)
      _ = _ := intervalIntegral.integral_add
        (main330_integrable (by norm_num) (by norm_num) (by norm_num)) correction330_integrable
  rw [heq]
  linarith [main330_integral_upper,correction330_integral_upper]

theorem high_le {L:ℝ} (hL:330 ≤ L) : high L ≤ (997/1000:ℝ) :=
  (high_antitone (by simp : (330:ℝ)∈Ici 330) hL hL).trans high330_le
#print axioms high_le
end E1NPlus
