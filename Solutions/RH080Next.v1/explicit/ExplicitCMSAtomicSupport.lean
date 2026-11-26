/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSFiniteAtomic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit.ZeroSummation

/-- Local summability itself supplies the countable nonzero support. No
countable enumeration or completed zero list is added as a premise. -/
theorem cutoff_ibp {ι : Type*} (w γ : ι → ℝ) (hw : Summable w)
    (a T : ℝ) (hγ : ∀i,w i≠0 → a<γ i ∧ γ i≤ T)
    (g g' : ℝ → ℝ) (hd : ∀x,HasDerivAt g (g' x) x) (hc : Continuous g') :
    Summable (fun i=> w i*g (γ i)) ∧ IntegrableOn (fun t=> countStep w γ t*g' t) (Ioc a T) ∧
      (∑'i,w i*g (γ i))=g T*(∑'i,w i)-∫t in Ioc a T,countStep w γ t*g' t:=by
  let S:=Function.support w
  letI : Countable S:=hw.countable_support.to_subtype
  have restricted : Summable (fun i : S=> w i):=hw.subtype _
  have supportProduct : Function.support (fun i=> w i*g (γ i))⊆S:=by
    intro i hi
    change w i≠0
    intro zero
    exact hi (by simp [zero])
  have stepEq (t : ℝ) : countStep (fun i : S=> w i) (fun i : S=>γ i) t=countStep w γ t:=by
    unfold countStep
    apply tsum_subtype_eq_of_support_subset (f:=fun i : ι=>if γ i≤t then w i else 0) (s:=S)
    intro i hi
    change w i≠0
    intro zero
    exact hi (by simp [zero])
  obtain ⟨sum,identity⟩:=countable_cutoff_ibp (fun i : S=> w i) (fun i : S=>γ i) restricted a T
    (fun i hi=> hγ i hi) g g' hd hc
  have fullSum : Summable (fun i=> w i*g (γ i)):=
    ((hasSum_subtype_iff_of_support_subset supportProduct).mp sum.hasSum).summable
  have integrable:=countStep_mul_integrable (fun i : S=> w i) (fun i : S=>γ i) restricted g' hc a T
  simp_rw [stepEq] at identity integrable
  rw [tsum_subtype_eq_of_support_subset supportProduct,tsum_subtype_support] at identity
  exact ⟨fullSum,integrable,identity⟩

#print axioms cutoff_ibp
end RH080Next.Explicit.ZeroSummation
