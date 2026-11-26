/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSAtomicSupport
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit.ZeroSummation

theorem countFamily_nonneg (T : ℝ) (ρ : CMSZeroIndex) : 0≤ cmsCountFamily T ρ:=by
  unfold cmsCountFamily cmsMultiplicity
  split_ifs <;> positivity

theorem countFamily_zero (hcount : SourceCMSZeroCounting) (a : ℝ) (zero : cmsPositiveZeroCount a=0) (ρ : CMSZeroIndex) :
    cmsCountFamily a ρ=0:=by
  have bound : cmsCountFamily a ρ≤ cmsPositiveZeroCount a:=by
    simpa only [Finset.sum_singleton,cmsPositiveZeroCount] using (hcount.1 a).sum_le_tsum {ρ} (fun i _=> countFamily_nonneg a i)
  rw [zero] at bound
  exact le_antisymm bound (countFamily_nonneg a ρ)

theorem countFamily_support (hcount : SourceCMSZeroCounting) (a T : ℝ) (zero : cmsPositiveZeroCount a=0)
    (ρ : CMSZeroIndex) (nonzero : cmsCountFamily T ρ≠0) : a<(ρ:ℂ).im ∧ (ρ:ℂ).im≤ T:=by
  have positive : 0<(ρ:ℂ).im ∧ (ρ:ℂ).im≤ T:=by
    by_contra h
    exact nonzero (by simp [cmsCountFamily,h])
  refine ⟨?_,positive.2⟩
  by_contra below
  have hz:=countFamily_zero hcount a zero ρ
  have small : (ρ:ℂ).im≤ a:=le_of_not_gt below
  have massZero : cmsMultiplicity ρ=0:=by simpa [cmsCountFamily,positive.1,small] using hz
  exact nonzero (by simp [cmsCountFamily,positive,massZero])

theorem actual_count_step (T t : ℝ) (ht : t≤ T) :
    countStep (cmsCountFamily T) (fun ρ : CMSZeroIndex=>(ρ:ℂ).im) t=cmsPositiveZeroCount t:=by
  apply tsum_congr
  intro ρ
  by_cases below : (ρ:ℂ).im≤ t
  · simp [cmsCountFamily,below,below.trans ht]
  · simp [cmsCountFamily,below]

/-- The actual right-closed CMS multiplicity count now satisfies finite-cutoff
partial summation by a kernel proof. No generic proof-scheme input is consumed. -/
theorem actual_c1_cutoff_ibp (hcount : SourceCMSZeroCounting) (a T : ℝ) (zero : cmsPositiveZeroCount a=0)
    (g g' : ℝ → ℝ) (hd : ∀x,HasDerivAt g (g' x) x) (hc : Continuous g') :
    Summable (fun ρ : CMSZeroIndex=> cmsCountFamily T ρ*g (ρ:ℂ).im) ∧
      IntegrableOn (fun t=> cmsPositiveZeroCount t*g' t) (Ioc a T) ∧
      (∑'ρ : CMSZeroIndex,cmsCountFamily T ρ*g (ρ:ℂ).im)=
        g T*cmsPositiveZeroCount T-∫t in Ioc a T,cmsPositiveZeroCount t*g' t:=by
  obtain ⟨sum,integ,identity⟩:=cutoff_ibp (cmsCountFamily T) (fun ρ : CMSZeroIndex=>(ρ:ℂ).im)
    (hcount.1 T) a T (countFamily_support hcount a T zero) g g' hd hc
  have eq : (fun t=> countStep (cmsCountFamily T) (fun ρ : CMSZeroIndex=>(ρ:ℂ).im) t*g' t)=ᵐ[volume.restrict (Ioc a T)]
      (fun t=> cmsPositiveZeroCount t*g' t):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [actual_count_step T t ht.2]
  exact ⟨sum,integ.congr eq,(identity.trans (by rw [integral_congr_ae eq];rfl))⟩

#print axioms actual_c1_cutoff_ibp
end RH080Next.Explicit.ZeroSummation
