/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineWindow
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open Real Set
namespace RH080Next.Primal
open RH080Next.Explicit

private theorem abs_positive_part_sub (x y : ℝ) : |max 0 x-max 0 y|≤|x-y| := by
  have h0 : LipschitzWith 0 (fun _ : ℝ => (0:ℝ)) := LipschitzWith.const 0
  have hi : LipschitzWith 1 (fun x : ℝ => x) := LipschitzWith.id
  have h := (h0.max hi).dist_le_mul x y
  simpa only [max_eq_right (by norm_num : (0:NNReal)≤1),NNReal.coe_one,one_mul,
    Real.dist_eq] using h

private theorem abs_hat_sub (x y : ℝ) : |hat x-hat y|≤|x-y| := by
  unfold hat
  apply (abs_positive_part_sub (1-|x|) (1-|y|)).trans
  rw [show 1-|x|-(1-|y|)=-(|x|-|y|) by ring,abs_neg]
  exact abs_abs_sub_abs_le_abs_sub x y

def affineLipschitzConstant (nodes : List ℚ) (m : ℕ) : ℝ :=
  (m:ℝ)*(|node nodes 0|+2*∑ j ∈ Finset.Ico 1 (nodes.length-1),|node nodes j|)

theorem affineLipschitzConstant_nonneg (nodes : List ℚ) (m : ℕ) :
    0≤affineLipschitzConstant nodes m := by unfold affineLipschitzConstant; positivity

/-- A finite global Lipschitz bound for the genuine finite spectrum. Sharpness
is unnecessary: the finite-grid BV consumer only needs its error to vanish. -/
theorem abs_affineSpectrum_sub_le (nodes : List ℚ) (m : ℕ) (x y : ℝ) :
    |affineSpectrum nodes m x-affineSpectrum nodes m y|≤
      affineLipschitzConstant nodes m*|x-y| := by
  have hshift (j : ℝ) : |hat ((m:ℝ)*x-j)-hat ((m:ℝ)*y-j)|≤(m:ℝ)*|x-y| := by
    apply (abs_hat_sub _ _).trans_eq
    rw [show (m:ℝ)*x-j-((m:ℝ)*y-j)=(m:ℝ)*(x-y) by ring,abs_mul,
      abs_of_nonneg (Nat.cast_nonneg m)]
  have hsum : (∑ j ∈ Finset.Ico 1 (nodes.length-1),
      |node nodes j*((hat ((m:ℝ)*x-j)-hat ((m:ℝ)*y-j))+
        (hat ((m:ℝ)*x+j)-hat ((m:ℝ)*y+j)))|)≤
      ∑ j ∈ Finset.Ico 1 (nodes.length-1),|node nodes j| * (2*(m:ℝ)*|x-y|) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hminus := hshift (j:ℝ)
    have hplus := hshift (-(j:ℝ))
    simp only [sub_neg_eq_add] at hplus
    exact (abs_add_le _ _).trans (by linarith)
  have he : affineSpectrum nodes m x-affineSpectrum nodes m y=
      node nodes 0*(hat ((m:ℝ)*x)-hat ((m:ℝ)*y))+
        ∑ j ∈ Finset.Ico 1 (nodes.length-1),
          node nodes j*((hat ((m:ℝ)*x-j)-hat ((m:ℝ)*y-j))+
            (hat ((m:ℝ)*x+j)-hat ((m:ℝ)*y+j))) := by
    unfold affineSpectrum
    rw [show node nodes 0*hat ((m:ℝ)*x)+(∑ j ∈ Finset.Ico 1 (nodes.length-1),
      node nodes j*(hat ((m:ℝ)*x-j)+hat ((m:ℝ)*x+j)))-
      (node nodes 0*hat ((m:ℝ)*y)+(∑ j ∈ Finset.Ico 1 (nodes.length-1),
        node nodes j*(hat ((m:ℝ)*y-j)+hat ((m:ℝ)*y+j))))=
      node nodes 0*(hat ((m:ℝ)*x)-hat ((m:ℝ)*y))+
        ((∑ j ∈ Finset.Ico 1 (nodes.length-1),node nodes j*(hat ((m:ℝ)*x-j)+hat ((m:ℝ)*x+j)))-
          ∑ j ∈ Finset.Ico 1 (nodes.length-1),node nodes j*(hat ((m:ℝ)*y-j)+hat ((m:ℝ)*y+j))) by ring,
      ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hfirst : |node nodes 0*(hat ((m:ℝ)*x)-hat ((m:ℝ)*y))|≤
      |node nodes 0| * (m:ℝ)*|x-y| := by
    rw [abs_mul]
    calc
      _ ≤ |node nodes 0| * ((m:ℝ)*|x-y|) :=
        mul_le_mul_of_nonneg_left (by simpa using hshift 0) (abs_nonneg _)
      _ = _ := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply (add_le_add hfirst ((Finset.abs_sum_le_sum_abs _ _).trans hsum)).trans_eq
  unfold affineLipschitzConstant
  rw [← Finset.sum_mul]
  ring

/-- The normalized spectrum's positive part is globally Lipschitz, as used by
the source-free finite-atomic BV limit. -/
theorem normalized_positive_affine_lipschitz (nodes : List ℚ) (m : ℕ) :
    ∃ K : NNReal, LipschitzWith K
      (fun x : ℝ => max 0 (affineSpectrum nodes m (1+(radius nodes m-1)*x))) := by
  refine ⟨(affineLipschitzConstant nodes m*|radius nodes m-1|).toNNReal,?_⟩
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [Real.dist_eq,Real.dist_eq]
  apply (abs_positive_part_sub _ _).trans
  apply (abs_affineSpectrum_sub_le nodes m _ _).trans_eq
  rw [show 1+(radius nodes m-1)*x-(1+(radius nodes m-1)*y)=
    (radius nodes m-1)*(x-y) by ring,abs_mul]
  ring

#print axioms abs_affineSpectrum_sub_le
#print axioms normalized_positive_affine_lipschitz
end RH080Next.Primal
