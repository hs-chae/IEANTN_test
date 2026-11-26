/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import W4FFTPolynomial
import ChordQuadrature
import ExplicitNormSourceBridge
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
noncomputable section
open scoped BigOperators
namespace RH080Next.Primal.W4FFTKernel
open RH080Next.FFT.IntegerModel RH080Next.Explicit

lemma coefficient_eq_integerNode (j : Nat) : W4.coefficient j = WindowPV.Data.integerNode j := by
  rfl

lemma actual_node_eq_coefficient (j : Nat) (hj : j<2520) :
    node WindowPV.Data.affineNodes j = realCoefficient j := by
  have hs : WindowPV.Data.affineNodes[j]? = some (WindowPV.Data.rationalNode j) := by
    rw [WindowPV.Data.affineNodes_eq_map]
    simp [show j<2521 by omega]
  unfold node
  rw [List.getD_eq_getElem?_getD, hs]
  simp only [Option.getD_some]
  rw [realCoefficient, coefficient_eq_integerNode]
  simp [WindowPV.Data.rationalNode, WindowPV.Data.scale]

lemma actual_terminal : node WindowPV.Data.affineNodes 2520 = 0 := by
  unfold node WindowPV.Data.affineNodes
  rw [List.getD_append_right _ _ _ _ (by rw [WindowPV.Data.nodes_length])]
  rw [WindowPV.Data.nodes_length]
  norm_num

/-- The mathematical polynomial uses exactly the locked rational nodes. -/
theorem nodalPolynomial_eq_series (y : ℝ) :
    nodalPolynomial WindowPV.Data.affineNodes y = cosineSeries 2520 realCoefficient y := by
  unfold cosineSeries
  rw [Finset.sum_range_eq_add_Ico _ (by decide : 0<2520)]
  unfold nodalPolynomial
  rw [WindowPV.Data.affineNodes_length]
  norm_num only [Nat.reduceSub]
  rw [actual_node_eq_coefficient 0 (by decide)]
  simp only [seriesWeight, frequency, Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one, one_mul, ite_true]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hJ := Finset.mem_Ico.mp hj
  rw [actual_node_eq_coefficient j hJ.2]
  simp only [seriesWeight, if_neg (show j≠0 by omega), frequency]
  ring

theorem series_period : cosineSeries 2520 realCoefficient 1 = cosineSeries 2520 realCoefficient 0 := by
  unfold cosineSeries
  apply Finset.sum_congr rfl
  intro j hj
  have hp : Real.cos (frequency j) = 1 := by
    convert Real.cos_nat_mul_two_pi j using 1 <;> unfold frequency <;> congr 1 <;> ring
  simp [hp]

def quadNumerator : Nat := ∑j ∈ Finset.range 2520, 20*j*j*(W4.coefficient j).natAbs

/-- Generic identity interpreting the source's finite scalar accumulator. -/
theorem range_foldl_sum (n : Nat) (f : Nat → Nat) :
    (List.range n).foldl (fun a j => a+f j) 0 = ∑j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]

/-- Genuine second derivative budget, on the actual signed coefficients. -/
theorem curvature_bound :
    (∑j ∈ Finset.range 2520, |seriesWeight realCoefficient j| *(frequency j)^2) ≤
      4*(quadNumerator:ℝ)/10000000000000000 := by
  have he : 4*(quadNumerator:ℝ)/10000000000000000 =
      ∑j ∈ Finset.range 2520, 80*(j:ℝ)^2*((W4.coefficient j).natAbs:ℝ)/10000000000000000 := by
    unfold quadNumerator
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  apply Finset.sum_le_sum
  intro j hj
  have hp : Real.pi^2 ≤ 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d20]
  have hf : (frequency j)^2 ≤ 40*(j:ℝ)^2 := by
    unfold frequency
    nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg (j:ℝ))]
  have hw : |seriesWeight realCoefficient j| ≤ 2*|realCoefficient j| := by
    by_cases hz : j=0
    · subst j
      simp only [seriesWeight, ite_true, one_mul]
      linarith [abs_nonneg (realCoefficient 0)]
    · simp [seriesWeight, hz, abs_mul]
  calc
    _ ≤ (2*|realCoefficient j|)*(40*(j:ℝ)^2) :=
      mul_le_mul hw hf (sq_nonneg _) (by positivity)
    _ = _ := by
      rw [realCoefficient, abs_div, abs_of_pos (by norm_num : (0:ℝ)<10000000000000000), ← natAbs_cast]
      ring

theorem periodic_integral_bound (G : Nat) (hG : 0<G) :
    (∫ y in (0:ℝ)..1, |nodalPolynomial WindowPV.Data.affineNodes y|) ≤
      (∑k ∈ Finset.range G, |cosineSeries 2520 realCoefficient ((k:ℝ)/G)|)/(G:ℝ) +
        (quadNumerator:ℝ)/(3*10000000000000000*(G:ℝ)^2) := by
  simp_rw [nodalPolynomial_eq_series]
  have h := cosine_series_abs_chord_quadrature 2520 (seriesWeight realCoefficient) frequency G hG series_period
  change (∫ y in (0:ℝ)..1, |cosineSeries 2520 realCoefficient y|) ≤ _ at h
  have hc := div_le_div_of_nonneg_right curvature_bound (by positivity : (0:ℝ)≤12*(G:ℝ)^2)
  apply h.trans
  apply add_le_add le_rfl
  convert hc using 1 <;> ring

#print axioms nodalPolynomial_eq_series
#print axioms curvature_bound
#print axioms periodic_integral_bound
end RH080Next.Primal.W4FFTKernel
