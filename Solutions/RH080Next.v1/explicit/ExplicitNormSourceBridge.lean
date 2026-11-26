/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFourierPair
import Mathlib.Data.List.GetD

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

/-- Literal general analytic norm identity in BR v2 Lemma fourier-norm,
equation eq:pair. N=5m and the rational nodes are arbitrary. This named
literature input is not claimed to have its periodization proof formalized here.
It contains no particular witness or numerical norm cap. -/
def SourceBRFourierNormFive : Prop :=
  ∀ nodes : List ℚ, ∀ m : ℕ, 0 < m → nodes.length = 5*m+1 →
    node nodes (5*m) = 0 →
      (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|) =
        ∫ y in (0:ℝ)..1, |nodalPolynomial nodes y|

theorem affine_inverse_norm_mesh_invariant (nodes : List ℚ) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) :
    (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|) =
      ∫ u : ℝ, |inverseCosine (affineSpectrum nodes n) u| := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  let r : ℝ := (n:ℝ)/(m:ℝ)
  have hr : 0 < r := div_pos hn' hm'
  have heq : (fun u : ℝ => |inverseCosine (affineSpectrum nodes m) u|) =
      (fun u : ℝ => r*|inverseCosine (affineSpectrum nodes n) (r*u)|) := by
    funext u
    rw [inverseCosine_affineSpectrum_mesh_dilation nodes m n hm hn u,
      abs_mul, abs_of_pos hr]
  rw [heq, integral_const_mul, Measure.integral_comp_mul_left (fun u : ℝ => |inverseCosine (affineSpectrum nodes n) u|) r]
  rw [abs_of_pos (inv_pos.mpr hr)]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

theorem affine_norm_eq_periodic_of_five_mesh (hsource : SourceBRFourierNormFive)
    (nodes : List ℚ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hlen : nodes.length = 5*n+1) (hlast : node nodes (5*n) = 0) :
    (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|) =
      ∫ y in (0:ℝ)..1, |nodalPolynomial nodes y| := by
  rw [affine_inverse_norm_mesh_invariant nodes m n hm hn]
  exact hsource nodes n hn hlen hlast

@[simp] theorem node_append_zeros (nodes : List ℚ) (k j : ℕ) :
    node (nodes ++ List.replicate k 0) j = node nodes j := by
  unfold node
  by_cases hj : j < nodes.length
  · rw [List.getD_append _ _ _ _ hj]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have hrep : (List.replicate k (0:ℚ)).getD (j-nodes.length) 0 = 0 := by
      simpa only [List.getD_eq_getElem?_getD] using
        List.getElem?_getD_replicate_default_eq (d := (0:ℚ)) k (j-nodes.length)
    rw [hrep, List.getD_eq_default nodes 0 (by omega)]

private theorem sum_nodes_append_zeros (nodes : List ℚ) (k : ℕ)
    (hlen : 2 ≤ nodes.length) (hlast : node nodes (nodes.length-1) = 0) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.Ico 1 ((nodes ++ List.replicate k 0).length-1),
      node (nodes ++ List.replicate k 0) j*f j) =
    ∑ j ∈ Finset.Ico 1 (nodes.length-1), node nodes j*f j := by
  simp only [node_append_zeros, List.length_append, List.length_replicate]
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_Ico] at *
    omega
  · intro j hj hjnot
    have hjl : nodes.length-1 ≤ j := by
      simp only [Finset.mem_Ico] at *
      omega
    by_cases heq : j = nodes.length-1
    · rw [heq, hlast, zero_mul]
    · have hzero : node nodes j = 0 := by
        unfold node
        rw [List.getD_eq_default _ _ (by omega)]
        norm_num
      rw [hzero, zero_mul]

theorem affineSpectrum_append_zeros (nodes : List ℚ) (k m : ℕ)
    (hlen : 2 ≤ nodes.length) (hlast : node nodes (nodes.length-1) = 0) :
    affineSpectrum (nodes ++ List.replicate k 0) m = affineSpectrum nodes m := by
  funext v
  unfold affineSpectrum
  rw [node_append_zeros, sum_nodes_append_zeros nodes k hlen hlast]

theorem nodalPolynomial_append_zeros (nodes : List ℚ) (k : ℕ)
    (hlen : 2 ≤ nodes.length) (hlast : node nodes (nodes.length-1) = 0) :
    nodalPolynomial (nodes ++ List.replicate k 0) = nodalPolynomial nodes := by
  funext v
  unfold nodalPolynomial
  rw [node_append_zeros, sum_nodes_append_zeros nodes k hlen hlast]

/-- Exact zero padding fits any shorter support into the literal published
support-five family, preserving both actual functions and the polynomial. -/
theorem affine_norm_eq_periodic_by_padding (hsource : SourceBRFourierNormFive)
    (nodes : List ℚ) (m : ℕ) (hm : 0 < m) (hlen : 2 ≤ nodes.length)
    (hlen5 : nodes.length ≤ 5*m+1) (hlast : node nodes (nodes.length-1) = 0) :
    (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|) =
      ∫ y in (0:ℝ)..1, |nodalPolynomial nodes y| := by
  let k := 5*m+1-nodes.length
  have hlen' : (nodes ++ List.replicate k 0).length = 5*m+1 := by simp [k]; omega
  have hlast' : node (nodes ++ List.replicate k 0) (5*m) = 0 := by
    rw [node_append_zeros]
    by_cases heq : 5*m = nodes.length-1
    · rw [heq, hlast]
    · unfold node
      rw [List.getD_eq_default _ _ (by omega)]
      norm_num
  have h := hsource (nodes ++ List.replicate k 0) m hm hlen' hlast'
  rw [affineSpectrum_append_zeros nodes k m hlen hlast,
    nodalPolynomial_append_zeros nodes k hlen hlast] at h
  exact h

end RH080Next.Explicit
