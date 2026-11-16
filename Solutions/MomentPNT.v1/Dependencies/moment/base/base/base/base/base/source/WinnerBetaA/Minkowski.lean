/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace WinnerBetaA.Minkowski
open Real

noncomputable def rawAmplitude (a₁ a₂ m₁ m₂ T x : ℝ) : ℝ :=
  (a₁ * (x*T)^((1:ℝ)/6) * log (x*T) + a₂) *
    sqrt ((m₁*x*T+m₂*T)*log T) + sqrt (x*T)

noncomputable def kernelBracket (a₁ a₂ m₁ m₂ H x : ℝ) : ℝ :=
  sqrt (m₁*x+m₂) * (x^((1:ℝ)/6)*(1+|log x|/log H) +
    a₂/(a₁*H^((1:ℝ)/6)*log H)) +
      1/(a₁*H^((1:ℝ)/6)*log H*sqrt (log H))*sqrt x

noncomputable def normalizationScale (T : ℝ) : ℝ :=
  T^((1:ℝ)/6)*sqrt T*log T*sqrt (log T)

/-- The normalized subconvexity factor is bounded uniformly in T using absolute log x. -/
theorem factor_bound {a₁ a₂ H T x : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂)
    (hH : 1 < H) (hHT : H ≤ T) (hx : 0 < x) :
    |a₁*(x*T)^((1:ℝ)/6)*log (x*T)+a₂| / (a₁*T^((1:ℝ)/6)*log T) ≤
      x^((1:ℝ)/6)*(1+|log x|/log H) + a₂/(a₁*H^((1:ℝ)/6)*log H) := by
  have hT : 1 < T := hH.trans_le hHT
  have hH0 : 0 < H := by linarith
  have hT0 : 0 < T := by linarith
  have hlH : 0 < log H := log_pos hH
  have hlT : 0 < log T := log_pos hT
  have hl : log H ≤ log T := log_le_log hH0 hHT
  have hwH : 0 < H^((1:ℝ)/6) := rpow_pos_of_pos hH0 _
  have hwT : 0 < T^((1:ℝ)/6) := rpow_pos_of_pos hT0 _
  have hw : H^((1:ℝ)/6) ≤ T^((1:ℝ)/6) := rpow_le_rpow hH0.le hHT (by norm_num)
  have hdenH : 0 < a₁*H^((1:ℝ)/6)*log H := by positivity
  have hdenT : 0 < a₁*T^((1:ℝ)/6)*log T := by positivity
  have hden : a₁*H^((1:ℝ)/6)*log H ≤ a₁*T^((1:ℝ)/6)*log T := by gcongr
  have hr0 : a₂/(a₁*T^((1:ℝ)/6)*log T) ≤ a₂/(a₁*H^((1:ℝ)/6)*log H) :=
    div_le_div_of_nonneg_left ha₂ hdenH hden
  have hlogratio : |log x|/log T ≤ |log x|/log H :=
    div_le_div_of_nonneg_left (abs_nonneg _) hlH hl
  have habslog : |log (x*T)| ≤ log T + |log x| := by
    rw [log_mul hx.ne' hT0.ne']
    have hh := abs_add_le (log x) (log T)
    rw [abs_of_pos hlT] at hh
    linarith
  have habs : |a₁*(x*T)^((1:ℝ)/6)*log (x*T)+a₂| ≤
      a₁*x^((1:ℝ)/6)*T^((1:ℝ)/6)*(log T+|log x|)+a₂ := by
    calc
      _ ≤ |a₁*(x*T)^((1:ℝ)/6)*log (x*T)|+|a₂| := abs_add_le _ _
      _ = a₁*(x*T)^((1:ℝ)/6)*|log (x*T)|+a₂ := by
        rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg ha₂]
      _ ≤ a₁*(x*T)^((1:ℝ)/6)*(log T+|log x|)+a₂ := by gcongr
      _ = _ := by rw [mul_rpow hx.le hT0.le]; ring
  calc
    _ ≤ (a₁*x^((1:ℝ)/6)*T^((1:ℝ)/6)*(log T+|log x|)+a₂) /
        (a₁*T^((1:ℝ)/6)*log T) := div_le_div_of_nonneg_right habs hdenT.le
    _ = x^((1:ℝ)/6)*(1+|log x|/log T) + a₂/(a₁*T^((1:ℝ)/6)*log T) := by
      field_simp
    _ ≤ _ := by
      have hxpow : 0 ≤ x^((1:ℝ)/6) := (rpow_pos_of_pos hx _).le
      nlinarith [mul_le_mul_of_nonneg_left hlogratio hxpow]

/-- The second Minkowski summand has a separately decreasing normalized coefficient. -/
theorem residual_bound {a₁ H T : ℝ} (ha₁ : 0 < a₁)
    (hH : 1 < H) (hHT : H ≤ T) :
    1/(a₁*T^((1:ℝ)/6)*log T*sqrt (log T)) ≤
      1/(a₁*H^((1:ℝ)/6)*log H*sqrt (log H)) := by
  have hH0 : 0 < H := by linarith
  have hT : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hlH : 0 < log H := log_pos hH
  have hlT : 0 < log T := log_pos hT
  have hl : log H ≤ log T := log_le_log hH0 hHT
  have hw : H^((1:ℝ)/6) ≤ T^((1:ℝ)/6) := rpow_le_rpow hH0.le hHT (by norm_num)
  have hs : sqrt (log H) ≤ sqrt (log T) := sqrt_le_sqrt hl
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

/-- The scale squared is exactly the original logT^3*T^(4/3) denominator. -/
theorem normalizationScale_sq {T : ℝ} (hT : 1 < T) :
    normalizationScale T ^ 2 = log T ^ 3 * T^((4:ℝ)/3) := by
  have hT0 : 0 < T := by linarith
  have hlT : 0 < log T := log_pos hT
  have hp : (T^((1:ℝ)/6))^2*T = T^((4:ℝ)/3) := by
    calc
      _ = (T^((1:ℝ)/6)*T^((1:ℝ)/6))*T^(1:ℝ) := by rw [rpow_one]; ring
      _ = T^(((1:ℝ)/6)+1/6)*T^(1:ℝ) := by
        rw [← rpow_add hT0]
      _ = T^((((1:ℝ)/6)+1/6)+1) := (rpow_add hT0 _ _).symm
      _ = _ := by congr 1; norm_num
  unfold normalizationScale
  rw [mul_pow, mul_pow, mul_pow, sq_sqrt hT0.le, sq_sqrt hlT.le]
  calc
    _ = ((T^((1:ℝ)/6))^2*T)*log T^3 := by ring
    _ = _ := by rw [hp]; ring

/-- Uniform normalized raw Minkowski amplitude; absolute values avoid any sign shortcut. -/
theorem amplitude_bound {a₁ a₂ m₁ m₂ H T x : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hH : 1 < H) (hHT : H ≤ T) (hx : 0 < x) :
    |rawAmplitude a₁ a₂ m₁ m₂ T x| / (a₁*normalizationScale T) ≤
      kernelBracket a₁ a₂ m₁ m₂ H x := by
  have hT : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hlT : 0 < log T := log_pos hT
  have hwT : 0 < T^((1:ℝ)/6) := rpow_pos_of_pos hT0 _
  have hsT : 0 < sqrt T := sqrt_pos.2 hT0
  have hslog : 0 < sqrt (log T) := sqrt_pos.2 hlT
  have hD : 0 ≤ m₁*x+m₂ := by positivity
  have hscale : 0 < a₁*normalizationScale T := by unfold normalizationScale; positivity
  have hroot : sqrt ((m₁*x*T+m₂*T)*log T) = sqrt (m₁*x+m₂)*sqrt T*sqrt (log T) := by
    rw [show (m₁*x*T+m₂*T)*log T = ((m₁*x+m₂)*T)*log T by ring,
      sqrt_mul (mul_nonneg hD hT0.le), sqrt_mul hD]
  have habs : |rawAmplitude a₁ a₂ m₁ m₂ T x| ≤
      |a₁*(x*T)^((1:ℝ)/6)*log (x*T)+a₂| * sqrt ((m₁*x*T+m₂*T)*log T) + sqrt (x*T) := by
    unfold rawAmplitude
    have h := abs_add_le
      ((a₁*(x*T)^((1:ℝ)/6)*log (x*T)+a₂)*sqrt ((m₁*x*T+m₂*T)*log T)) (sqrt (x*T))
    simpa only [abs_mul, abs_of_nonneg (sqrt_nonneg _)] using h
  calc
    _ ≤ (|a₁*(x*T)^((1:ℝ)/6)*log (x*T)+a₂| * sqrt ((m₁*x*T+m₂*T)*log T) + sqrt (x*T)) /
        (a₁*normalizationScale T) := div_le_div_of_nonneg_right habs hscale.le
    _ = sqrt (m₁*x+m₂) *
        (|a₁*(x*T)^((1:ℝ)/6)*log (x*T)+a₂|/(a₁*T^((1:ℝ)/6)*log T)) +
          (1/(a₁*T^((1:ℝ)/6)*log T*sqrt (log T)))*sqrt x := by
      rw [hroot, sqrt_mul hx.le]
      unfold normalizationScale
      field_simp
    _ ≤ kernelBracket a₁ a₂ m₁ m₂ H x := by
      have h1 := mul_le_mul_of_nonneg_left (factor_bound ha₁ ha₂ hH hHT hx) (sqrt_nonneg (m₁*x+m₂))
      have h2 := mul_le_mul_of_nonneg_right (residual_bound ha₁ hH hHT) (sqrt_nonneg x)
      unfold kernelBracket
      linarith

/-- New uniform-kernel majorization before Gaussian integration; all T and x are covered. -/
theorem normalized_raw_bound {a₁ a₂ m₁ m₂ H T x : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hH : 1 < H) (hHT : H ≤ T) (hx : 0 < x) :
    rawAmplitude a₁ a₂ m₁ m₂ T x ^ 2 / (log T^3*T^((4:ℝ)/3)) ≤
      a₁^2 * kernelBracket a₁ a₂ m₁ m₂ H x ^ 2 := by
  have hT : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hlT : 0 < log T := log_pos hT
  have hs : 0 < normalizationScale T := by unfold normalizationScale; positivity
  have hden : 0 < log T^3*T^((4:ℝ)/3) := by positivity
  have hp := amplitude_bound ha₁ ha₂ hm₁ hm₂ hH hHT hx
  have hsq := pow_le_pow_left₀
    (show 0 ≤ |rawAmplitude a₁ a₂ m₁ m₂ T x|/(a₁*normalizationScale T) by positivity) hp 2
  rw [div_pow, sq_abs, mul_pow, normalizationScale_sq hT] at hsq
  have hb := (div_le_iff₀ (mul_pos (sq_pos_of_pos ha₁) hden)).mp hsq
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ kernelBracket a₁ a₂ m₁ m₂ H x ^ 2 * (a₁^2*(log T^3*T^((4:ℝ)/3))) := hb
    _ = _ := by ring

/-- Consume the independently sourced raw F_X Minkowski inequality, not a new U oracle. -/
theorem normalized_minkowski {F a₁ a₂ m₁ m₂ H T x : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hH : 1 < H) (hHT : H ≤ T) (hx : 0 < x)
    (hsource : F ≤ rawAmplitude a₁ a₂ m₁ m₂ T x ^ 2) :
    F / (log T^3*T^((4:ℝ)/3)) ≤ a₁^2*kernelBracket a₁ a₂ m₁ m₂ H x ^ 2 := by
  have hT : 1 < T := hH.trans_le hHT
  have hlT : 0 < log T := log_pos hT
  have hden : 0 < log T^3*T^((4:ℝ)/3) := by positivity
  exact (div_le_div_of_nonneg_right hsource hden.le).trans
    (normalized_raw_bound ha₁ ha₂ hm₁ hm₂ hH hHT hx)

noncomputable def envelopeBracket (M₁ M₂ h r₀ r₁ x : ℝ) : ℝ :=
  sqrt (M₁*x+M₂)*(x^((1:ℝ)/6)*(1+|log x|/h)+r₀)+r₁*sqrt x

/-- Source-derived coefficients can be enlarged independently, without interpolating data. -/
theorem bracket_of_scalar_bounds {a₁ a₂ m₁ m₂ H x M₁ M₂ h r₀ r₁ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hH : 1 < H) (hx : 0 < x)
    (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (hh : 0 < h) (hhH : h ≤ log H)
    (hr₀ : a₂/(a₁*H^((1:ℝ)/6)*log H) ≤ r₀)
    (hr₁ : 1/(a₁*H^((1:ℝ)/6)*log H*sqrt (log H)) ≤ r₁) :
    kernelBracket a₁ a₂ m₁ m₂ H x ≤ envelopeBracket M₁ M₂ h r₀ r₁ x := by
  have hlogH : 0 < log H := log_pos hH
  have hH0 : 0 < H := by linarith
  have hroot : sqrt (m₁*x+m₂) ≤ sqrt (M₁*x+M₂) := by
    apply sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_right hM₁ hx.le]
  have hratio : |log x|/log H ≤ |log x|/h :=
    div_le_div_of_nonneg_left (abs_nonneg _) hh hhH
  have hxp : 0 ≤ x^((1:ℝ)/6) := (rpow_pos_of_pos hx _).le
  have hinner : x^((1:ℝ)/6)*(1+|log x|/log H)+a₂/(a₁*H^((1:ℝ)/6)*log H) ≤
      x^((1:ℝ)/6)*(1+|log x|/h)+r₀ := by
    nlinarith [mul_le_mul_of_nonneg_left hratio hxp]
  have hinner0 : 0 ≤ x^((1:ℝ)/6)*(1+|log x|/log H)+a₂/(a₁*H^((1:ℝ)/6)*log H) := by positivity
  have hprod := mul_le_mul hroot hinner hinner0 (sqrt_nonneg (M₁*x+M₂))
  have hres := mul_le_mul_of_nonneg_right hr₁ (sqrt_nonneg x)
  unfold kernelBracket envelopeBracket
  linarith

/-- Exact logarithmic coordinate, before separating positive and negative y. -/
theorem envelopeBracket_exp (M₁ M₂ h r₀ r₁ y : ℝ) :
    envelopeBracket M₁ M₂ h r₀ r₁ (exp y) =
      sqrt (M₁*exp y+M₂)*(exp (y/6)*(1+|y|/h)+r₀)+r₁*exp (y/2) := by
  unfold envelopeBracket
  rw [log_exp, ← exp_half]
  have hr : (exp y)^((1:ℝ)/6) = exp (y/6) := by
    rw [rpow_def_of_pos (exp_pos y), log_exp]
    congr 1
    ring
  rw [hr]

noncomputable def rationalKernel (y : ℝ) : ℝ :=
  exp (2*y-(601/2500:ℝ)*exp (2*y))*
    (sqrt ((645/1000:ℝ)*exp y+23/250)*
      (exp (y/6)*(1+|y|/28)+681/500000)+(23/250000)*exp (y/2))^2

noncomputable def signedKernel (sign y : ℝ) : ℝ :=
  exp (2*y-(601/2500:ℝ)*exp (2*y))*
    (sqrt ((645/1000:ℝ)*exp y+23/250)*
      (exp (y/6)*(1+sign*y/28)+681/500000)+(23/250000)*exp (y/2))^2

/-- Concrete scalar majorization produces precisely the finite-integration target. -/
theorem rational_kernel_bound {a₁ a₂ m₁ m₂ H y : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hH : 1 < H)
    (hM₁ : m₁ ≤ (645/1000:ℝ)) (hM₂ : m₂ ≤ (23/250:ℝ)) (hhH : (28:ℝ) ≤ log H)
    (hr₀ : a₂/(a₁*H^((1:ℝ)/6)*log H) ≤ (681/500000:ℝ))
    (hr₁ : 1/(a₁*H^((1:ℝ)/6)*log H*sqrt (log H)) ≤ (23/250000:ℝ)) :
    exp (2*y-(601/2500:ℝ)*exp (2*y))*kernelBracket a₁ a₂ m₁ m₂ H (exp y)^2 ≤ rationalKernel y := by
  have hb := bracket_of_scalar_bounds ha₁ ha₂ hH (exp_pos y) hM₁ hM₂
    (show (0:ℝ)<28 by norm_num) hhH hr₀ hr₁
  have hknonneg : 0 ≤ kernelBracket a₁ a₂ m₁ m₂ H (exp y) := by
    have hlH : 0 < log H := log_pos hH
    have hH0 : 0 < H := by linarith
    unfold kernelBracket
    positivity
  have hs := pow_le_pow_left₀ hknonneg hb 2
  rw [envelopeBracket_exp] at hs
  exact mul_le_mul_of_nonneg_left hs (exp_pos _).le

/-- The two signed AST integrands meet exactly at zero, with their source domains explicit. -/
theorem rationalKernel_nonpos {y : ℝ} (hy : y ≤ 0) : rationalKernel y = signedKernel (-1) y := by
  simp only [rationalKernel, signedKernel, abs_of_nonpos hy, neg_one_mul]

theorem rationalKernel_nonneg {y : ℝ} (hy : 0 ≤ y) : rationalKernel y = signedKernel 1 y := by
  simp only [rationalKernel, signedKernel, abs_of_nonneg hy, one_mul]

#print axioms normalized_minkowski
end WinnerBetaA.Minkowski
