/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AffineLipschitz
import AffinePositiveVariation
import ExplicitAtomicBV
set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Primal
open RH080Next.Explicit

def positiveRightWing (nodes : List ℚ) (m : ℕ) (z : ℝ) : ℝ :=
  max 0 (affineSpectrum nodes m (1+(radius nodes m-1)*z))
def positiveLeftWing (nodes : List ℚ) (m : ℕ) (z : ℝ) : ℝ :=
  max 0 (affineSpectrum nodes m (-radius nodes m+(radius nodes m-1)*z))

theorem positiveLeftWing_reflection (nodes : List ℚ) (m : ℕ) (z : ℝ) :
    positiveLeftWing nodes m z=positiveRightWing nodes m (1-z) := by
  unfold positiveLeftWing positiveRightWing
  rw [show -radius nodes m+(radius nodes m-1)*z=
    -(1+(radius nodes m-1)*(1-z)) by ring,affineSpectrum_even]

/-- Every aligned normalized grid has the exact source H variation. -/
theorem rightWing_grid_variation (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hmN : m<nodes.length-1)
    (hlast : node nodes (nodes.length-1)=0) (G : ℕ) (hG : 0<G) :
    positiveRightWing nodes m 0+
      (∑ i ∈ Finset.range ((nodes.length-1-m)*G),
        max 0 (positiveRightWing nodes m (((i:ℝ)+1)/((nodes.length-1-m)*G:ℕ))-
          positiveRightWing nodes m ((i:ℝ)/((nodes.length-1-m)*G:ℕ))))=
      nodalH nodes m := by
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hG0 : (G:ℝ)≠0 := by exact_mod_cast hG.ne'
  have hD0 : ((nodes.length-1-m:ℕ):ℝ)≠0 := by exact_mod_cast (show nodes.length-1-m≠0 by omega)
  have hR : radius nodes m-1=((nodes.length-1-m:ℕ):ℝ)/(m:ℝ) := by
    unfold radius
    rw [Nat.cast_sub hmN.le]
    field_simp
    <;> ring
  have hpoint (i : ℕ) :
      positiveRightWing nodes m ((i:ℝ)/((nodes.length-1-m)*G:ℕ))=
        refinedPositiveValue nodes m G i := by
    unfold positiveRightWing refinedPositiveValue
    rw [hR,Nat.cast_mul]
    congr 2
    field_simp
  have h0 : positiveRightWing nodes m 0=refinedPositiveValue nodes m G 0 := by
    simpa using hpoint 0
  rw [h0,← affine_refined_positive_variation nodes m G hlen hm hG hmN.le hlast]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (i:ℝ)+1=((i+1:ℕ):ℝ) by push_cast; rfl,hpoint (i+1),hpoint i]

private theorem sum_increments (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n,(f (i+1)-f i))=f n-f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

private theorem positive_reversal (a b : ℝ) :
    max 0 (a-b)=max 0 (b-a)-(b-a) := by
  rcases le_total a b with h | h
  · rw [max_eq_left (sub_nonpos.mpr h),max_eq_right (sub_nonneg.mpr h)]; ring
  · rw [max_eq_right (sub_nonneg.mpr h),max_eq_left (sub_nonpos.mpr h)]; ring

/-- Initial height plus positive variation is invariant under reversing a
finite path. This handles left-wing orientation and both endpoint values. -/
theorem finite_positive_variation_reverse (f : ℕ → ℝ) (n : ℕ) :
    f n+(∑ i ∈ Finset.range n,max 0 (f (n-(i+1))-f (n-i)))=
      f 0+∑ i ∈ Finset.range n,max 0 (f (i+1)-f i) := by
  have hsum : (∑ i ∈ Finset.range n,max 0 (f (n-(i+1))-f (n-i)))=
      ∑ i ∈ Finset.range n,max 0 (f i-f (i+1)) := by
    rw [← Finset.sum_range_reflect (fun i => max 0 (f i-f (i+1))) n]
    apply Finset.sum_congr rfl
    intro i hi
    have hn := Finset.mem_range.mp hi
    rw [show n-1-i=n-(i+1) by omega,show n-(i+1)+1=n-i by omega]
  rw [hsum]
  have hterms : (∑ i ∈ Finset.range n,max 0 (f i-f (i+1)))=
      ∑ i ∈ Finset.range n,(max 0 (f (i+1)-f i)-(f (i+1)-f i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact positive_reversal (f i) (f (i+1))
  rw [hterms,Finset.sum_sub_distrib,sum_increments]
  ring

theorem leftWing_grid_variation (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hmN : m<nodes.length-1)
    (hlast : node nodes (nodes.length-1)=0) (G : ℕ) (hG : 0<G) :
    positiveLeftWing nodes m 0+
      (∑ i ∈ Finset.range ((nodes.length-1-m)*G),
        max 0 (positiveLeftWing nodes m (((i:ℝ)+1)/((nodes.length-1-m)*G:ℕ))-
          positiveLeftWing nodes m ((i:ℝ)/((nodes.length-1-m)*G:ℕ))))=
      nodalH nodes m := by
  let n : ℕ := (nodes.length-1-m)*G
  have hn : 0<n := Nat.mul_pos (by omega) hG
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hpoint (i : ℕ) (hi : i≤n) :
      positiveLeftWing nodes m ((i:ℝ)/(n:ℝ))=
        positiveRightWing nodes m ((n-i:ℕ)/(n:ℝ)) := by
    rw [positiveLeftWing_reflection,Nat.cast_sub hi]
    congr 1
    field_simp
  have he : positiveLeftWing nodes m 0+
      (∑ i ∈ Finset.range n,max 0 (positiveLeftWing nodes m (((i:ℝ)+1)/(n:ℝ))-
        positiveLeftWing nodes m ((i:ℝ)/(n:ℝ))))=
      positiveRightWing nodes m 0+
      ∑ i ∈ Finset.range n,max 0 (positiveRightWing nodes m (((i:ℝ)+1)/(n:ℝ))-
        positiveRightWing nodes m ((i:ℝ)/(n:ℝ))) := by
    have hr := finite_positive_variation_reverse
      (fun i : ℕ => positiveRightWing nodes m ((i:ℝ)/(n:ℝ))) n
    simp only [Nat.cast_zero,zero_div,div_self hn0,Nat.cast_add,Nat.cast_one] at hr
    rw [positiveLeftWing_reflection,sub_zero]
    apply Eq.trans _ hr
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hin := Finset.mem_range.mp hi
    rw [show (i:ℝ)+1=((i+1:ℕ):ℝ) by push_cast; rfl,
      hpoint (i+1) (by omega),hpoint i hin.le]
  exact he.trans (rightWing_grid_variation nodes m hlen hm hmN hlast G hG)

theorem positiveLeftWing_lipschitz (nodes : List ℚ) (m : ℕ) :
    ∃ K : NNReal, LipschitzWith K (positiveLeftWing nodes m) := by
  obtain ⟨K,hK⟩ := normalized_positive_affine_lipschitz nodes m
  refine ⟨K,LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  rw [Real.dist_eq,Real.dist_eq,positiveLeftWing_reflection,positiveLeftWing_reflection]
  have h := hK.dist_le_mul (1-x) (1-y)
  simpa only [positiveRightWing,Real.dist_eq,
    show 1-x-(1-y)=-(x-y) by ring,abs_neg] using h

/-- Exact normalizing Jacobian for the actual exterior positive mass. -/
theorem integral_positiveRightWing (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hmN : m<nodes.length-1)
    (hlast : node nodes (nodes.length-1)=0) :
    (∫ z in (0:ℝ)..1, positiveRightWing nodes m z)=
      IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)/(2*(radius nodes m-1)) := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hR : 1<radius nodes m := by
    unfold radius
    apply (lt_div_iff₀ hm').mpr
    simpa using (show (m:ℝ)<((nodes.length-1:ℕ):ℝ) by exact_mod_cast hmN)
  have hc : Continuous (fun v : ℝ => max 0 (affineSpectrum nodes m v)) :=
    continuous_const.max (continuous_affineSpectrum nodes m)
  have hs := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume)
    (f := fun v : ℝ => max 0 (affineSpectrum nodes m v))
    (a := fun j : ℕ => (j:ℝ)/(m:ℝ)) hmN.le
    (fun j hj => hc.intervalIntegrable _ _)
  have hcells : (∑ j ∈ Finset.Ico m (nodes.length-1),
      ∫ v in (j:ℝ)/(m:ℝ)..((j+1:ℕ):ℝ)/(m:ℝ),max 0 (affineSpectrum nodes m v))=
      ∑ j ∈ Finset.Ico m (nodes.length-1),
        positiveChordArea (node nodes j) (node nodes (j+1))/(m:ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact integral_positive_affine_cell nodes m hlen hm hlast j (Finset.mem_Ico.mp hj).2
  rw [hs,div_self hm'.ne'] at hcells
  change (∫ v in (1:ℝ)..radius nodes m,max 0 (affineSpectrum nodes m v))=_ at hcells
  have hmass : 2*(∫ v in (1:ℝ)..radius nodes m,max 0 (affineSpectrum nodes m v))=
      IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m) := by
    rw [hcells,positiveLeak_affineSpectrum_eq_nodalPositiveArea nodes m hlen hm hmN.le hlast,
      ← Finset.sum_div]
    unfold nodalPositiveArea
    ring
  have hchange := intervalIntegral.smul_integral_comp_mul_add
    (fun v : ℝ => max 0 (affineSpectrum nodes m v)) (a := 0) (b := 1)
    (radius nodes m-1) 1
  simp only [smul_eq_mul,mul_zero,zero_add,mul_one,sub_add_cancel] at hchange
  have hfun : (fun z : ℝ => max 0 (affineSpectrum nodes m ((radius nodes m-1)*z+1)))=
      positiveRightWing nodes m := by
    funext z
    unfold positiveRightWing
    rw [add_comm]
  rw [hfun] at hchange
  apply (eq_div_iff (by positivity : (2*(radius nodes m-1))≠0)).mpr
  nlinarith

theorem integral_positiveLeftWing (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hmN : m<nodes.length-1)
    (hlast : node nodes (nodes.length-1)=0) :
    (∫ z in (0:ℝ)..1, positiveLeftWing nodes m z)=
      IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)/(2*(radius nodes m-1)) := by
  have he : positiveLeftWing nodes m=fun z : ℝ => positiveRightWing nodes m (1-z) :=
    funext (positiveLeftWing_reflection nodes m)
  rw [he,intervalIntegral.integral_comp_sub_left]
  simpa only [sub_self,sub_zero] using integral_positiveRightWing nodes m hlen hm hmN hlast

/-- The actual right spectrum wing satisfies the continuum atomic inequality,
consuming the exact H and J identities and a proved finite Lipschitz bound. -/
theorem rightWing_atomic_BV_bound {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (x w : ι → ℝ) (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hmN : m<nodes.length-1)
    (hlast : node nodes (nodes.length-1)=0) (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hx : ∀ p∈P,0<x p ∧ x p≤1) (hw : ∀ p∈P,0≤w p)
    (hcount : ∀ a b : ℝ,0≤a → a≤b → b≤1 →
      atomicPrefix P x w b-atomicPrefix P x w a≤B*(b-a)+C) :
    (∑ p ∈ P,w p*positiveRightWing nodes m (x p))≤
      B*(IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)/(2*(radius nodes m-1)))+
        C*nodalH nodes m := by
  obtain ⟨K,hK⟩ := normalized_positive_affine_lipschitz nodes m
  have h := finite_atomic_continuous_BV_bound P x w (positiveRightWing nodes m) hK.continuous
    (nodes.length-1-m) (by omega) B C (nodalH nodes m) (K:ℝ) hB hC K.property hx hw
    (fun t ht => le_max_left _ _)
    (fun a ha b hb => by simpa only [positiveRightWing,Real.dist_eq] using hK.dist_le_mul a b)
    hcount (fun G hG => (rightWing_grid_variation nodes m hlen hm hmN hlast G hG).le)
  rw [integral_positiveRightWing nodes m hlen hm hmN hlast] at h
  exact h

theorem leftWing_atomic_BV_bound {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (x w : ι → ℝ) (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hmN : m<nodes.length-1)
    (hlast : node nodes (nodes.length-1)=0) (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hx : ∀ p∈P,0<x p ∧ x p≤1) (hw : ∀ p∈P,0≤w p)
    (hcount : ∀ a b : ℝ,0≤a → a≤b → b≤1 →
      atomicPrefix P x w b-atomicPrefix P x w a≤B*(b-a)+C) :
    (∑ p ∈ P,w p*positiveLeftWing nodes m (x p))≤
      B*(IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)/(2*(radius nodes m-1)))+
        C*nodalH nodes m := by
  obtain ⟨K,hK⟩ := positiveLeftWing_lipschitz nodes m
  have h := finite_atomic_continuous_BV_bound P x w (positiveLeftWing nodes m) hK.continuous
    (nodes.length-1-m) (by omega) B C (nodalH nodes m) (K:ℝ) hB hC K.property hx hw
    (fun t ht => le_max_left _ _)
    (fun a ha b hb => by simpa only [Real.dist_eq] using hK.dist_le_mul a b)
    hcount (fun G hG => (leftWing_grid_variation nodes m hlen hm hmN hlast G hG).le)
  rw [integral_positiveLeftWing nodes m hlen hm hmN hlast] at h
  exact h

#print axioms rightWing_grid_variation
#print axioms finite_positive_variation_reverse
#print axioms leftWing_grid_variation
#print axioms integral_positiveRightWing
#print axioms integral_positiveLeftWing
#print axioms rightWing_atomic_BV_bound
#print axioms leftWing_atomic_BV_bound
end RH080Next.Primal
