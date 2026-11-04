/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldPointwise
namespace WinnerOldC4Source
open Real Set MeasureTheory
open WinnerOldFloors
set_option maxHeartbeats 0
noncomputable def smoothingR : ℝ := (1/2)/(1-1/(3000000000000-1))^2
noncomputable def omegaFactor (s u : ℝ) : ℝ :=
  smoothingR*exp (2*alpha-2*alpha*((s-d/u)/exp u)^2)

theorem omegaFactor_bounds {s u : ℝ} (hs : (3/4:ℝ)≤s) (hs' : s≤7/8) (hu : h≤u) :
    (499999/1000000:ℝ)*exp (2*alpha)≤omegaFactor s u ∧
      omegaFactor s u≤(501/1000:ℝ)*exp (2*alpha) := by
  have hu28 : (28:ℝ)≤u := h_lower.trans hu
  have hup : 0<u := by linarith
  have hd : d/u≤(1/8:ℝ) := (div_le_iff₀ hup).mpr (by unfold d;linarith)
  have hdp : 0≤d/u := by unfold d;positivity
  have hsp0 : 0≤s-d/u := by linarith
  have hsp : s-d/u≤1 := by linarith
  have hexp : (3000000000000:ℝ)≤exp u := by
    have he : exp h=(3000000000000:ℝ) := by unfold h;rw [exp_log (by norm_num)]
    rw [←he]
    exact exp_le_exp.mpr hu
  have hRatio : (s-d/u)/exp u≤(1/3000000000000:ℝ) :=
    div_le_div₀ (by norm_num) hsp (by norm_num) hexp
  have hRatio0 : 0≤(s-d/u)/exp u := div_nonneg hsp0 (exp_pos _).le
  have hsq : ((s-d/u)/exp u)^2≤(1/3000000000000:ℝ)^2 :=
    pow_le_pow_left₀ hRatio0 hRatio 2
  have hsmall : 2*alpha*((s-d/u)/exp u)^2≤(1/500000:ℝ) := by
    unfold alpha
    nlinarith
  have hsmall0 : 0≤2*alpha*((s-d/u)/exp u)^2 := by unfold alpha;positivity
  have hExpLo : (499999/500000:ℝ)≤exp (-2*alpha*((s-d/u)/exp u)^2) := by
    have hh:=add_one_le_exp (-2*alpha*((s-d/u)/exp u)^2)
    linarith
  have hExpHi : exp (-2*alpha*((s-d/u)/exp u)^2)≤1 :=
    exp_le_one_iff.mpr (by nlinarith)
  have hRlo : (1/2:ℝ)≤smoothingR := by norm_num [smoothingR]
  have hRhi : smoothingR≤(501/1000:ℝ) := by norm_num [smoothingR]
  have hprodLo := mul_le_mul hRlo hExpLo (by norm_num : (0:ℝ)≤499999/500000)
    (by norm_num [smoothingR] : 0≤smoothingR)
  have hprodHi := mul_le_mul hRhi hExpHi (exp_pos _).le (by norm_num : (0:ℝ)≤501/1000)
  have he : omegaFactor s u=exp (2*alpha)*(smoothingR*exp (-2*alpha*((s-d/u)/exp u)^2)) := by
    unfold omegaFactor
    rw [show 2*alpha-2*alpha*((s-d/u)/exp u)^2=2*alpha+(-2*alpha*((s-d/u)/exp u)^2) by ring,exp_add]
    ring
  rw [he]
  constructor
  · have hh:=mul_le_mul_of_nonneg_left hprodLo (exp_pos (2*alpha)).le
    norm_num only at hh
    nlinarith
  · have hh:=mul_le_mul_of_nonneg_left hprodHi (exp_pos (2*alpha)).le
    nlinarith

#print axioms omegaFactor_bounds
end WinnerOldC4Source
