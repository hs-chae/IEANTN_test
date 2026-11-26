/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSModulusCutoff
import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit.ZeroSummation

def positiveFamily (f : ℝ → ℝ) (ρ : CMSZeroIndex) : ℝ:=
  if 0<(ρ:ℂ).im then cmsMultiplicity ρ*|f (ρ:ℂ).im| else 0

theorem positiveFamily_nonneg (f : ℝ → ℝ) (ρ : CMSZeroIndex) : 0≤ positiveFamily f ρ:=by
  unfold positiveFamily cmsMultiplicity
  split_ifs <;> positivity

theorem ioc_integral_limit (f : ℝ → ℝ) (a : ℝ) (hf : IntegrableOn f (Ioi a)) :
    Tendsto (fun T : ℝ=>∫t in Ioc a T,f t) atTop (𝓝 (∫t in Ioi a,f t)):=by
  have limit:=intervalIntegral_tendsto_integral_Ioi a hf (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  apply limit.congr'
  filter_upwards [eventually_ge_atTop a] with T hT
  exact intervalIntegral.integral_of_le hT

/-- Positive-ordinate summability and the infinite bound are consequences of
all finite-cutoff bounds. No infinite zero sum is assumed convergent. -/
theorem actual_positive_infinite (hcount : SourceCMSZeroCounting) (a : ℝ) (ha : exp 1≤ a)
    (zero : cmsPositiveZeroCount a=0) (root : cmsQ a=0)
    (f f' : ℝ → ℝ) (hd : ∀x,HasDerivAt f (f' x) x) (hc : Continuous f')
    (main : IntegrableOn (fun t=> qDensity t*|f t|) (Ioi a))
    (error : IntegrableOn (fun t=> countError t*|f' t|) (Ioi a))
    (boundary : Tendsto (fun T : ℝ=>|f T| * cmsCountRemainder T) atTop (𝓝 0)) :
    Summable (positiveFamily f) ∧
      (∑'ρ : CMSZeroIndex,positiveFamily f ρ)≤
        (∫t in Ioi a,qDensity t*|f t|)+(∫t in Ioi a,countError t*|f' t|):=by
  let bound (T : ℝ):=|f T| * |cmsCountRemainder T| + (∫t in Ioc a T,qDensity t*|f t|)+(∫t in Ioc a T,countError t*|f' t|)
  let final : ℝ:=(∫t in Ioi a,qDensity t*|f t|)+(∫t in Ioi a,countError t*|f' t|)
  have boundaryAbs : Tendsto (fun T : ℝ=>|f T| * |cmsCountRemainder T|) atTop (𝓝 0):=by
    simpa only [abs_mul,abs_abs,abs_zero] using boundary.abs
  have limit : Tendsto bound atTop (𝓝 final):=by
    simpa only [zero_add] using (boundaryAbs.add (ioc_integral_limit _ a main)).add (ioc_integral_limit _ a error)
  have finiteBound (S : Finset CMSZeroIndex) : (∑ρ∈S,positiveFamily f ρ)≤ final:=by
    have covered : ∀ᶠT : ℝ in atTop,∀ρ∈S,(ρ:ℂ).im≤ T:=
      (S.eventually_all).mpr (fun ρ _=> eventually_ge_atTop (ρ:ℂ).im)
    have eventual : ∀ᶠT : ℝ in atTop,(∑ρ∈S,positiveFamily f ρ)≤ bound T:=by
      filter_upwards [covered,eventually_ge_atTop a] with T hT hTa
      obtain ⟨sum,estimate⟩:=actual_modulus_cutoff hcount a T ha hTa zero root f f' hd hc
      have same (ρ : CMSZeroIndex) (hρ : ρ∈S) : positiveFamily f ρ=cmsCountFamily T ρ*|f (ρ:ℂ).im|:=by
        simp [positiveFamily,cmsCountFamily,hT ρ hρ]
      calc
        (∑ρ∈S,positiveFamily f ρ)=∑ρ∈S,cmsCountFamily T ρ*|f (ρ:ℂ).im|:=Finset.sum_congr rfl same
        _≤∑'ρ : CMSZeroIndex,cmsCountFamily T ρ*|f (ρ:ℂ).im|:=sum.sum_le_tsum S (fun ρ _=> mul_nonneg (countFamily_nonneg T ρ) (abs_nonneg _))
        _≤ bound T:=estimate
    exact ge_of_tendsto limit eventual
  exact ⟨summable_of_sum_le (positiveFamily_nonneg f) finiteBound,Real.tsum_le_of_sum_le (positiveFamily_nonneg f) finiteBound⟩

#print axioms actual_positive_infinite
end RH080Next.Explicit.ZeroSummation
