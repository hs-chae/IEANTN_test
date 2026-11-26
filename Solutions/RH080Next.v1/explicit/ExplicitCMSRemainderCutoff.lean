/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSQCalculus
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit.ZeroSummation

theorem actual_c1_remainder_cutoff (hcount : SourceCMSZeroCounting) (a T : ℝ) (ha : 0< a) (hab : a≤ T)
    (zero : cmsPositiveZeroCount a=0) (root : cmsQ a=0)
    (g g' : ℝ → ℝ) (hd : ∀x,HasDerivAt g (g' x) x) (hc : Continuous g') :
    Summable (fun ρ : CMSZeroIndex=> cmsCountFamily T ρ*g (ρ:ℂ).im) ∧
      IntegrableOn (fun t=> qDensity t*g t) (Ioc a T) ∧
      IntegrableOn (fun t=> cmsCountRemainder t*g' t) (Ioc a T) ∧
      (∑'ρ : CMSZeroIndex,cmsCountFamily T ρ*g (ρ:ℂ).im)=
        g T*cmsCountRemainder T+(∫t in Ioc a T,qDensity t*g t)-(∫t in Ioc a T,cmsCountRemainder t*g' t):=by
  obtain ⟨sum,ni,nid⟩:=actual_c1_cutoff_ibp hcount a T zero g g' hd hc
  obtain ⟨qi,main,identity⟩:=q_cutoff_ibp a T ha hab g g' hd hc
  have ri : IntegrableOn (fun t=> cmsCountRemainder t*g' t) (Ioc a T):=by
    apply (ni.sub qi).congr
    filter_upwards [] with t
    change cmsPositiveZeroCount t*g' t-cmsQ t*g' t=(cmsPositiveZeroCount t-cmsQ t)*g' t
    ring
  have rid : (∫t in Ioc a T,cmsCountRemainder t*g' t)=
      (∫t in Ioc a T,cmsPositiveZeroCount t*g' t)-(∫t in Ioc a T,cmsQ t*g' t):=by
    rw [←integral_sub ni qi]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp [cmsCountRemainder]
    ring
  refine ⟨sum,main,ri,?_⟩
  rw [rid,identity,root,zero_mul,sub_zero,nid]
  dsimp [cmsCountRemainder]
  ring

#print axioms actual_c1_remainder_cutoff
end RH080Next.Explicit.ZeroSummation
