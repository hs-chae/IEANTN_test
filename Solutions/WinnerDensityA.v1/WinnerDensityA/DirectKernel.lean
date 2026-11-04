/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

open Complex MeasureTheory Set
namespace WinnerDirectKernel

noncomputable def zexp (z : ℂ) (u : ℝ) : ℂ := Complex.exp (z * (u : ℂ))

lemma zexp_deriv (z : ℂ) (u : ℝ) :
    HasDerivAt (zexp z) (z * zexp z u) u := by
  simpa only [zexp, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, mul_comm] using!
    ((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul z).cexp

lemma derivative_remainder (z : ℂ) (u : ℝ) (hz : z ≠ 0) (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ => zexp z t / (z^2 * (t : ℂ)^2))
      (zexp z u / (z * (u : ℂ)^2) - 2 * zexp z u / (z^2 * (u : ℂ)^3)) u := by
  have hc : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have hd := (zexp_deriv z u).fun_div
    (((Complex.ofRealCLM.hasDerivAt (x := u)).pow 2).const_mul (z^2)) (mul_ne_zero (pow_ne_zero 2 hz) (pow_ne_zero 2 hc))
  convert! hd using 1
  simp only [Pi.pow_apply, Complex.ofRealCLM_apply, Complex.ofReal_one, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, mul_one]
  field_simp [hz, hc]
  <;> ring

lemma integral_kernel_identity (z : ℂ) {v L : ℝ} (hz : z ≠ 0)
    (hv : 0 < v) (hL : v ≤ L) :
    zexp z L / (z * (L : ℂ)) + (∫ u in v..L, zexp z u / (z * (u : ℂ)^2)) =
      zexp z L / (z * (L : ℂ)) + zexp z L / (z^2 * (L : ℂ)^2) -
        zexp z v / (z^2 * (v : ℂ)^2) +
          (2 / z^2) * (∫ u in v..L, zexp z u / (u : ℂ)^3) := by
  have zcont : Continuous (zexp z) := by unfold zexp; fun_prop
  have h1 : IntervalIntegrable (fun u : ℝ => zexp z u / (z * (u : ℂ)^2)) volume v L := by
    apply ContinuousOn.intervalIntegrable_of_Icc hL
    apply zcont.continuousOn.div (by fun_prop)
    intro u hu
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hv.trans_le hu.1))
    exact mul_ne_zero hz (pow_ne_zero 2 hu0)
  have h2 : IntervalIntegrable (fun u : ℝ => 2 * zexp z u / (z^2 * (u : ℂ)^3)) volume v L := by
    apply ContinuousOn.intervalIntegrable_of_Icc hL
    apply (continuous_const.mul zcont).continuousOn.div (by fun_prop)
    intro u hu
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hv.trans_le hu.1))
    exact mul_ne_zero (pow_ne_zero 2 hz) (pow_ne_zero 3 hu0)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => derivative_remainder z u hz (by rw [uIcc_of_le hL] at hu; linarith [hu.1]))
    (h1.sub h2)
  rw [intervalIntegral.integral_sub h1 h2] at he
  have hrewrite : (∫ u in v..L, 2 * zexp z u / (z^2 * (u : ℂ)^3)) =
      (2 / z^2) * (∫ u in v..L, zexp z u / (u : ℂ)^3) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    field_simp
  rw [hrewrite] at he
  linear_combination he

#print axioms integral_kernel_identity
end WinnerDirectKernel
