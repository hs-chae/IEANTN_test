/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTButterfly
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
open Real
namespace RH080Next.FFT

/-- These are the rational values represented by the separately verified C
initializer's five base-10^9 limbs and sign. This mathematical definition does
not, by itself, assert correspondence with that C execution. -/
def rootSeed : ℂ :=
  ⟨999999999999929872242879801239728737/1000000000000000000000000000000000000,
    -374507028292384123903169179084/1000000000000000000000000000000000000⟩

private def theta : ℝ := 2*π/16777216

private theorem theta_bounds :
    (2*3.14159265358979323846/16777216:ℝ) ≤ theta ∧
      theta ≤ (2*3.14159265358979323847/16777216:ℝ) := by
  dsimp [theta]
  constructor <;> linarith [pi_gt_d20,pi_lt_d20]

private theorem theta_small : 0≤theta ∧ theta≤(4/10000000:ℝ) := by
  have h := theta_bounds
  constructor <;> linarith

private theorem rootSeed_re_cos :
    |rootSeed.re-cos theta| ≤ (4/1000000000000000000000000000:ℝ) := by
  have ht := theta_bounds
  have hsmall := theta_small
  have hl2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2*3.14159265358979323846/16777216) ht.1 2
  have hu2 := pow_le_pow_left₀ hsmall.1 ht.2 2
  have hu4 := pow_le_pow_left₀ hsmall.1 hsmall.2 4
  have hpoly : |rootSeed.re-(1-theta^2/2)|≤(2/1000000000000000000000000000:ℝ) := by
    rw [abs_le]
    norm_num [rootSeed] at *
    constructor <;> nlinarith
  have hc := cos_bound (show |theta|≤1 by rw [abs_of_nonneg hsmall.1]; linarith)
  rw [abs_of_nonneg hsmall.1] at hc
  have herr : |cos theta-(1-theta^2/2)|≤(2/1000000000000000000000000000:ℝ) := by
    nlinarith
  calc
    _ ≤ |rootSeed.re-(1-theta^2/2)|+|(1-theta^2/2)-cos theta| := abs_sub_le _ _ _
    _ ≤ _ := by rw [abs_sub_comm (1-theta^2/2)]; linarith

private theorem rootSeed_im_sin :
    |rootSeed.im+sin theta| ≤ (4/1000000000000000000000000000:ℝ) := by
  have ht := theta_bounds
  have hsmall := theta_small
  have hl3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2*3.14159265358979323846/16777216) ht.1 3
  have hu3 := pow_le_pow_left₀ hsmall.1 ht.2 3
  have hu5 := pow_le_pow_left₀ hsmall.1 hsmall.2 5
  have hpoly : |rootSeed.im+(theta-theta^3/6)|≤(2/1000000000000000000000000000:ℝ) := by
    rw [abs_le]
    norm_num [rootSeed] at *
    constructor <;> nlinarith
  have hs := sin_bound (show |theta|≤1 by rw [abs_of_nonneg hsmall.1]; linarith)
  rw [abs_of_nonneg hsmall.1] at hs
  have herr : |sin theta-(theta-theta^3/6)|≤(2/1000000000000000000000000000:ℝ) := by
    nlinarith
  calc
    _ = |(rootSeed.im+(theta-theta^3/6))+(sin theta-(theta-theta^3/6))| := by congr 1; ring
    _ ≤ |rootSeed.im+(theta-theta^3/6)|+|sin theta-(theta-theta^3/6)| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- Kernel bound on the actual initializer's represented seed. The source
verification must consume its separate execution-to-representation theorem. -/
theorem rootSeed_error : ‖rootSeed-negativeRoot 16777216‖≤
    (1/100000000000000000000000000:ℝ) := by
  have hr : (negativeRoot 16777216).re=cos theta := by
    simp [negativeRoot,Complex.exp_re,Complex.div_re,Complex.div_im,
      Complex.mul_re,Complex.mul_im,theta,neg_div]
  have hi : (negativeRoot 16777216).im= -sin theta := by
    simp [negativeRoot,Complex.exp_im,Complex.div_re,Complex.div_im,
      Complex.mul_re,Complex.mul_im,theta,neg_div]
  have h := Complex.norm_le_abs_re_add_abs_im (rootSeed-negativeRoot 16777216)
  simp only [Complex.sub_re,Complex.sub_im,hr,hi,sub_neg_eq_add] at h
  exact h.trans (by linarith [rootSeed_re_cos,rootSeed_im_sin])

#print axioms rootSeed_error
end RH080Next.FFT
