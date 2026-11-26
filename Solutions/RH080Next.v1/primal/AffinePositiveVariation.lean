/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AffinePositiveCellArea
set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Primal
open RH080Next.Explicit

private theorem sum_increments (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (f (k+1)-f k))=f n-f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

private theorem sum_positive_increments_mono (f : ℕ → ℝ) (hf : Monotone f) (n : ℕ) :
    (∑ k ∈ Finset.range n, max 0 (f (k+1)-f k))=max 0 (f n-f 0) := by
  have he : (∑ k ∈ Finset.range n, max 0 (f (k+1)-f k))=
      ∑ k ∈ Finset.range n, (f (k+1)-f k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact max_eq_right (sub_nonneg.mpr (hf (Nat.le_succ k)))
  rw [he,sum_increments,max_eq_right (sub_nonneg.mpr (hf (Nat.zero_le n)))]

private theorem sum_positive_increments_anti (f : ℕ → ℝ) (hf : Antitone f) (n : ℕ) :
    (∑ k ∈ Finset.range n, max 0 (f (k+1)-f k))=max 0 (f n-f 0) := by
  rw [max_eq_left (sub_nonpos.mpr (hf (Nat.zero_le n)))]
  apply Finset.sum_eq_zero
  intro k hk
  exact max_eq_left (sub_nonpos.mpr (hf (Nat.le_succ k)))

/-- Uniform refinement preserves the exact positive variation of a single
positive-part affine cell, even when the affine segment crosses zero. -/
theorem positive_chord_refined_variation (a b : ℝ) (G : ℕ) (hG : 0<G) :
    (∑ k ∈ Finset.range G,
      max 0 (max 0 (chord a b ((k+1:ℕ)/(G:ℝ)))-
        max 0 (chord a b ((k:ℝ)/(G:ℝ)))))=
      max 0 (max 0 b-max 0 a) := by
  have hG' : (0:ℝ)<G := by exact_mod_cast hG
  let f : ℕ → ℝ := fun k => max 0 (chord a b ((k:ℝ)/(G:ℝ)))
  have hchord (t : ℝ) : chord a b t=a+(b-a)*t := by unfold chord; ring
  have hEnd0 : f 0=max 0 a := by simp [f,chord]
  have hEndG : f G=max 0 b := by simp [f,chord,hG'.ne']
  change (∑ k ∈ Finset.range G,max 0 (f (k+1)-f k))=_
  rw [← hEnd0,← hEndG]
  rcases le_total a b with hab | hba
  · apply sum_positive_increments_mono
    intro i j hij
    dsimp [f]
    rw [hchord,hchord]
    apply max_le_max le_rfl
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hG'.le
  · apply sum_positive_increments_anti
    intro i j hij
    dsimp [f]
    rw [hchord,hchord]
    apply max_le_max le_rfl
    apply add_le_add_right
    apply mul_le_mul_of_nonpos_left _ (sub_nonpos.mpr hba)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hG'.le

private theorem affineSpectrum_refined_cell_value (nodes : List ℚ) (m G j k : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hG : 0<G)
    (hlast : node nodes (nodes.length-1)=0) (hj : j<nodes.length-1) (hk : k≤G) :
    affineSpectrum nodes m (((j:ℝ)+(k:ℝ)/(G:ℝ))/(m:ℝ))=
      chord (node nodes j) (node nodes (j+1)) ((k:ℝ)/(G:ℝ)) := by
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hG' : (0:ℝ)<G := by exact_mod_cast hG
  have ht0 : (0:ℝ)≤(k:ℝ)/(G:ℝ) := by positivity
  have ht1 : (k:ℝ)/(G:ℝ)≤1 := (div_le_one hG').mpr (by exact_mod_cast hk)
  have hv : (m:ℝ)*(((j:ℝ)+(k:ℝ)/(G:ℝ))/(m:ℝ))=j+(k:ℝ)/(G:ℝ) := by field_simp
  rw [affineSpectrum_cell_phase nodes m hlen hlast j hj _
    (by rw [hv]; linarith) (by rw [hv]; linarith),hv]
  unfold chord
  ring

/-- Actual spectrum values in every cell, not nodal samples merely asserted to
match an interpolation model. -/
theorem affine_cell_refined_positive_variation (nodes : List ℚ) (m G j : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hG : 0<G)
    (hlast : node nodes (nodes.length-1)=0) (hj : j<nodes.length-1) :
    (∑ k ∈ Finset.range G,
      max 0 (max 0 (affineSpectrum nodes m (((j:ℝ)+(k+1:ℕ)/(G:ℝ))/(m:ℝ)))-
        max 0 (affineSpectrum nodes m (((j:ℝ)+(k:ℝ)/(G:ℝ))/(m:ℝ)))))=
      max 0 (max 0 (node nodes (j+1))-max 0 (node nodes j)) := by
  rw [← positive_chord_refined_variation (node nodes j) (node nodes (j+1)) G hG]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [affineSpectrum_refined_cell_value nodes m G j (k+1) hlen hm hG hlast hj (by omega),
    affineSpectrum_refined_cell_value nodes m G j k hlen hm hG hlast hj hk'.le]

private theorem sum_range_blocks (f : ℕ → ℝ) (B G : ℕ) :
    (∑ r ∈ Finset.range (B*G), f r)=
      ∑ b ∈ Finset.range B, ∑ k ∈ Finset.range G, f (b*G+k) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [show (B+1)*G=B*G+G by ring,Finset.sum_range_add,Finset.sum_range_succ,ih]

private theorem affineSpectrum_one_eq_node (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hmN : m≤nodes.length-1)
    (hlast : node nodes (nodes.length-1)=0) : affineSpectrum nodes m 1=node nodes m := by
  by_cases hlt : m<nodes.length-1
  · have h := affineSpectrum_cell_phase nodes m hlen hlast m hlt 1
      (by simp) (by simp)
    simpa using h
  · have he : m=nodes.length-1 := by omega
    have hr : radius nodes m=1 := by
      unfold radius
      rw [← he]
      exact div_self (by exact_mod_cast hm.ne')
    rw [affineSpectrum_eq_zero_of_radius_le nodes m hlen hm 1 (by rw [hr]; norm_num),
      he,hlast]

def refinedPositiveValue (nodes : List ℚ) (m G r : ℕ) : ℝ :=
  max 0 (affineSpectrum nodes m (1+(r:ℝ)/((m:ℝ)*(G:ℝ))))

/-- The entire physically sampled spectrum has exactly the same positive
variation on every uniform refinement. This is the actual H quantity needed
by the finite-atomic interval/BV argument, without charging a new error term
for each mesh cell. -/
theorem affine_refined_positive_variation (nodes : List ℚ) (m G : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hG : 0<G)
    (hmN : m≤nodes.length-1) (hlast : node nodes (nodes.length-1)=0) :
    refinedPositiveValue nodes m G 0+
      (∑ r ∈ Finset.range ((nodes.length-1-m)*G),
        max 0 (refinedPositiveValue nodes m G (r+1)-refinedPositiveValue nodes m G r))=
      nodalH nodes m := by
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hG0 : (G:ℝ)≠0 := by exact_mod_cast hG.ne'
  have hcoord (b k : ℕ) :
      1+((b*G+k:ℕ):ℝ)/((m:ℝ)*(G:ℝ))=
        (((m+b:ℕ):ℝ)+(k:ℝ)/(G:ℝ))/(m:ℝ) := by
    push_cast
    field_simp
    <;> ring
  have hblock (b : ℕ) (hb : b∈Finset.range (nodes.length-1-m)) :
      (∑ k ∈ Finset.range G,
        max 0 (refinedPositiveValue nodes m G (b*G+k+1)-
          refinedPositiveValue nodes m G (b*G+k)))=
        max 0 (max 0 (node nodes (m+b+1))-max 0 (node nodes (m+b))) := by
    have hj : m+b<nodes.length-1 := by have h:=Finset.mem_range.mp hb; omega
    rw [← affine_cell_refined_positive_variation nodes m G (m+b) hlen hm hG hlast hj]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show b*G+k+1=b*G+(k+1) by omega]
    unfold refinedPositiveValue
    rw [hcoord b (k+1),hcoord b k]
  have hfirst : refinedPositiveValue nodes m G 0=max 0 (node nodes m) := by
    simp only [refinedPositiveValue,Nat.cast_zero,zero_div,add_zero,
      affineSpectrum_one_eq_node nodes m hlen hm hmN hlast]
  rw [hfirst,sum_range_blocks]
  calc
    _ = max 0 (node nodes m)+
        ∑ b ∈ Finset.range (nodes.length-1-m),
          max 0 (max 0 (node nodes (m+b+1))-max 0 (node nodes (m+b))) := by
      congr 1
      apply Finset.sum_congr rfl
      exact hblock
    _ = nodalH nodes m := by
      unfold nodalH
      rw [Finset.sum_Ico_eq_sum_range]

#print axioms positive_chord_refined_variation
#print axioms affine_cell_refined_positive_variation
#print axioms affine_refined_positive_variation
end RH080Next.Primal
