/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSRemainderCutoff
import ExplicitCMSModulus
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit.ZeroSummation

def countError (t : ℝ) : ℝ:=(3/20:ℝ)*log t+3

theorem countError_continuousOn (a T : ℝ) (ha : 0< a) : ContinuousOn countError (Icc a T):=by
  intro x hx
  have nonzero : x≠0:=ne_of_gt (lt_of_lt_of_le ha hx.1)
  unfold countError
  fun_prop

/-- Absolute values at zeros are handled by smooth approximation at a finite
cutoff. Epsilon is removed before the cutoff tends to infinity. -/
theorem actual_modulus_cutoff (hcount : SourceCMSZeroCounting) (a T : ℝ) (ha : exp 1≤ a) (hab : a≤ T)
    (zero : cmsPositiveZeroCount a=0) (root : cmsQ a=0)
    (f f' : ℝ → ℝ) (hd : ∀x,HasDerivAt f (f' x) x) (hc : Continuous f') :
    Summable (fun ρ : CMSZeroIndex=> cmsCountFamily T ρ*|f (ρ:ℂ).im|) ∧
      (∑'ρ : CMSZeroIndex,cmsCountFamily T ρ*|f (ρ:ℂ).im|)≤
        |f T| * |cmsCountRemainder T| + (∫t in Ioc a T,qDensity t*|f t|)+(∫t in Ioc a T,countError t*|f' t|):=by
  have apos : 0< a:=(exp_pos 1).trans_le ha
  have fc : Continuous f:=continuous_iff_continuousAt.mpr (fun x=>(hd x).continuousAt)
  have mainInt : IntegrableOn (fun t=> qDensity t*|f t|) (Ioc a T):=
    ((qDensity_continuousOn a T apos).mul fc.abs.continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have errorInt : IntegrableOn (fun t=> countError t*|f' t|) (Ioc a T):=
    ((countError_continuousOn a T apos).mul hc.abs.continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have densityInt : IntegrableOn (fun t=>|qDensity t|) (Ioc a T):=
    (qDensity_continuousOn a T apos).abs.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have smooth (ε : ℝ) (hε : 0<ε) :=actual_c1_remainder_cutoff hcount a T apos hab zero root
    (cmsSmoothModulus f ε) (cmsSmoothModulusDeriv f f' ε)
    (fun x=> cmsSmoothModulus_hasDerivAt (hd x) hε) (cmsSmoothModulusDeriv_continuous hd hc hε)
  have summable : Summable (fun ρ : CMSZeroIndex=> cmsCountFamily T ρ*|f (ρ:ℂ).im|):=by
    apply Summable.of_nonneg_of_le (fun ρ=> mul_nonneg (countFamily_nonneg T ρ) (abs_nonneg _))
      (fun ρ=> mul_le_mul_of_nonneg_left (cmsSmoothModulus_bounds f (show (0:ℝ)<1 by norm_num) (ρ:ℂ).im).1 (countFamily_nonneg T ρ))
      (smooth 1 (by norm_num)).1
  let A : ℝ:=∑'ρ : CMSZeroIndex,cmsCountFamily T ρ*|f (ρ:ℂ).im|
  let B : ℝ:=|f T| * |cmsCountRemainder T| + (∫t in Ioc a T,qDensity t*|f t|)+(∫t in Ioc a T,countError t*|f' t|)
  let C : ℝ:=|cmsCountRemainder T| + (∫t in Ioc a T,|qDensity t|)
  have bound (ε : ℝ) (hε : 0<ε) : A≤ B+ε*C:=by
    obtain ⟨smoothSum,smoothMain,smoothError,identity⟩:=smooth ε hε
    have seriesLe : A≤∑'ρ : CMSZeroIndex,cmsCountFamily T ρ*cmsSmoothModulus f ε (ρ:ℂ).im:=
      summable.tsum_le_tsum (fun ρ=> mul_le_mul_of_nonneg_left (cmsSmoothModulus_bounds f hε (ρ:ℂ).im).1 (countFamily_nonneg T ρ)) smoothSum
    have boundary : cmsSmoothModulus f ε T*cmsCountRemainder T≤|f T| * |cmsCountRemainder T| + ε*|cmsCountRemainder T|:=by
      have first:=mul_le_mul_of_nonneg_left (le_abs_self (cmsCountRemainder T)) (cmsSmoothModulus_pos f hε T).le
      have second:=mul_le_mul_of_nonneg_right (cmsSmoothModulus_bounds f hε T).2 (abs_nonneg (cmsCountRemainder T))
      nlinarith
    have mainBound : (∫t in Ioc a T,qDensity t*cmsSmoothModulus f ε t)≤
        (∫t in Ioc a T,qDensity t*|f t|)+ε*(∫t in Ioc a T,|qDensity t|):=by
      have point (t : ℝ) : qDensity t*cmsSmoothModulus f ε t≤ qDensity t*|f t| + ε*|qDensity t|:=by
        obtain ⟨lo,hi⟩:=cmsSmoothModulus_uniform_error f hε t
        have first:=mul_le_mul_of_nonneg_right (le_abs_self (qDensity t)) lo
        have second:=mul_le_mul_of_nonneg_left hi (abs_nonneg (qDensity t))
        nlinarith
      have comparison:=setIntegral_mono_on smoothMain (mainInt.add (densityInt.const_mul ε)) measurableSet_Ioc (fun t _=> point t)
      change (∫t in Ioc a T,qDensity t*cmsSmoothModulus f ε t)≤
        (∫t in Ioc a T,qDensity t*|f t|+ε*|qDensity t|) at comparison
      rw [integral_add mainInt (densityInt.const_mul ε),integral_const_mul] at comparison
      exact comparison
    have errorBound : -(∫t in Ioc a T,cmsCountRemainder t*cmsSmoothModulusDeriv f f' ε t)≤
        (∫t in Ioc a T,countError t*|f' t|):=by
      have comparison:=setIntegral_mono_on smoothError.neg errorInt measurableSet_Ioc (fun t ht=> by
        have count:=hcount.2.2 t (ha.trans ht.1.le)
        change |cmsCountRemainder t|≤ countError t at count
        have derivative:=cmsSmoothModulusDeriv_abs_le f f' hε t
        have product:=mul_le_mul count derivative (abs_nonneg _) ((abs_nonneg _).trans count)
        have bound:=neg_le_abs (cmsCountRemainder t*cmsSmoothModulusDeriv f f' ε t)
        rw [abs_mul] at bound
        exact bound.trans product)
      change (∫t in Ioc a T,-(cmsCountRemainder t*cmsSmoothModulusDeriv f f' ε t))≤
        (∫t in Ioc a T,countError t*|f' t|) at comparison
      rw [integral_neg] at comparison
      exact comparison
    rw [identity] at seriesLe
    dsimp [B,C]
    nlinarith
  have limit : Tendsto (fun ε : ℝ=> B+ε*C) (𝓝[>] (0:ℝ)) (𝓝 B):=by
    have cont : Continuous (fun ε : ℝ=> B+ε*C):=by fun_prop
    have atzero : Tendsto (fun ε : ℝ=> B+ε*C) (𝓝 (0:ℝ)) (𝓝 (B+0*C)):=cont.continuousAt
    simpa only [zero_mul,add_zero] using atzero.mono_left nhdsWithin_le_nhds
  have eventual : ∀ᶠ ε in (𝓝[>] (0:ℝ)),A≤B+ε*C:=by
    filter_upwards [(self_mem_nhdsWithin : Ioi (0:ℝ)∈𝓝[>] (0:ℝ))] with ε hε
    exact bound ε hε
  exact ⟨summable,ge_of_tendsto limit eventual⟩

#print axioms actual_modulus_cutoff
end RH080Next.Explicit.ZeroSummation
