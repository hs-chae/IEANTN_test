import BoxPrefactorSecond
import Mathlib.Analysis.Calculus.LHopital

/-! A genuine second-order right limit, not just a displayed formal series. -/
namespace RHOcticPush.BoxGamma
open Real Filter Set
open scoped Topology

lemma prefactor_differentiable_near_zero :
    ∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ prefactor s := by
  have hc0 : ContinuousAt (fun s : ℝ => Real.cos (Real.pi * s / 2)) 0 := by fun_prop
  have hc := hc0.eventually_ne (by norm_num : Real.cos (Real.pi * (0 : ℝ) / 2) ≠ 0)
  filter_upwards [hc, Iio_mem_nhds (show (0 : ℝ) < 2 by norm_num)] with s hs hs2
  change s < 2 at hs2
  have hG : DifferentiableAt ℝ Real.Gamma (2 - s) := Real.differentiableAt_Gamma (by
    intro n hn
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  have hG0 : Real.Gamma (2 - s) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hP := HasDerivAt.const_rpow (show (0 : ℝ) < 2 by norm_num)
    ((hasDerivAt_id s).neg)
  have hg := hG.hasDerivAt.comp s ((hasDerivAt_id s).const_sub 2)
  have hc := (((hasDerivAt_id s).const_mul Real.pi).div_const 2).cos
  exact (hP.div (hg.mul hc) (mul_ne_zero hG0 hs)).differentiableAt

theorem prefactor_second_coefficient :
    Tendsto (fun s : ℝ =>
      (prefactor s - 1 - (1 - Real.eulerMascheroniConstant - Real.log 2) * s) / s^2)
      (𝓝[>] 0)
      (𝓝 (((1 - Real.eulerMascheroniConstant - Real.log 2)^2 + 1 + Real.pi^2 / 12) / 2)) := by
  let a : ℝ := 1 - Real.eulerMascheroniConstant - Real.log 2
  let b : ℝ := a^2 + 1 + Real.pi^2 / 12
  have hff : ∀ᶠ s : ℝ in 𝓝[>] 0,
      HasDerivAt (fun s : ℝ => prefactor s - 1 - a*s) (deriv prefactor s - a) s := by
    filter_upwards [prefactor_differentiable_near_zero.filter_mono nhdsWithin_le_nhds] with s hs
    exact ((hs.hasDerivAt.sub_const 1).sub ((hasDerivAt_id s).const_mul a)).congr_deriv
      (by simp)
  have hgg : ∀ᶠ s : ℝ in 𝓝[>] 0,
      HasDerivAt (fun s : ℝ => s^2) (2*s) s := by
    filter_upwards [] with s
    exact ((hasDerivAt_id s).pow 2).congr_deriv (by norm_num)
  have hgn : ∀ᶠ s : ℝ in 𝓝[>] 0, 2*s ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_ne_zero (by norm_num) (ne_of_gt hs)
  have hfa : Tendsto (fun s : ℝ => prefactor s - 1 - a*s) (𝓝[>] 0) (𝓝 0) := by
    have h := ((prefactor_hasDerivAt.continuousAt.tendsto.sub_const 1).sub
      ((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0)).const_mul a)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa using h
  have hga : Tendsto (fun s : ℝ => s^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0)).pow 2).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hdiv : Tendsto (fun s : ℝ => (deriv prefactor s - a) / (2*s))
      (𝓝[>] 0) (𝓝 (b/2)) := by
    have h := prefactor_second.tendsto_slope_zero_right
    have h0 : deriv prefactor 0 = a := prefactor_hasDerivAt.deriv
    have ht : Tendsto (fun s : ℝ => (deriv prefactor s - a)/s) (𝓝[>] 0) (𝓝 b) := by
      simpa [h0, smul_eq_mul, div_eq_mul_inv, mul_comm, b, a] using h
    have ht2 := ht.div_const 2
    apply ht2.congr'
    filter_upwards [] with s
    ring
  exact HasDerivAt.lhopital_zero_nhdsGT hff hgg hgn hfa hga hdiv

#print axioms prefactor_second_coefficient
end RHOcticPush.BoxGamma
