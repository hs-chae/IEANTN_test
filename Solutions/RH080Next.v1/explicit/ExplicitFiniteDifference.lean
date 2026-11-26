/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineFourier

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private theorem second_difference_identity (a C : ℕ → ℝ)
    (h0 : C 0 = 1)
    (hrec : ∀ k : ℕ, C (k+2) = 2*C 1*C (k+1)-C k) (N : ℕ) :
    (1-C 1)*(a 0+2*∑ j ∈ Finset.Ico 1 (N+2), a j*C j) =
      a 0-a 1 + (∑ j ∈ Finset.Ico 1 (N+1),
        (2*a j-a (j-1)-a (j+1))*C j) +
      (2*a (N+1)-a N)*C (N+1)-a (N+1)*C (N+2) := by
  induction N with
  | zero =>
    simp only [Nat.zero_add, Nat.reduceAdd, Finset.Ico_self, Finset.sum_empty,
      Finset.sum_Ico_succ_top (by omega : 1 ≤ 1), hrec 0, h0]
    ring
  | succ N ih =>
    have hp := Finset.sum_Ico_succ_top (f := fun j => a j*C j) (by omega : 1 ≤ N+2)
    have hd := Finset.sum_Ico_succ_top
      (f := fun j => (2*a j-a (j-1)-a (j+1))*C j) (by omega : 1 ≤ N+1)
    rw [show N+1+2 = (N+2)+1 by omega, hp,
      show N+1+1 = (N+1)+1 by omega, hd]
    have heq : (1-C 1)*(a 0+2*((∑ j ∈ Finset.Ico 1 (N+2), a j*C j) + a (N+2)*C (N+2))) =
        (1-C 1)*(a 0+2*∑ j ∈ Finset.Ico 1 (N+2), a j*C j) +
          2*a (N+2)*(1-C 1)*C (N+2) := by ring
    rw [heq, ih, hrec (N+1)]
    simp only [Nat.add_sub_cancel]
    ring

private theorem cos_nat_recurrence (q : ℝ) (k : ℕ) :
    cos ((k+2:ℕ)*q) = 2*cos q*cos ((k+1:ℕ)*q)-cos ((k:ℝ)*q) := by
  have hplus : ((k+2:ℕ):ℝ)*q = ((k+1:ℕ):ℝ)*q+q := by push_cast; ring
  have hminus : (k:ℝ)*q = ((k+1:ℕ):ℝ)*q-q := by push_cast; ring
  rw [hplus, hminus, cos_add, cos_sub]
  ring

/-- Discrete integration by parts, including both endpoint slope jumps. -/
theorem nodalPolynomial_second_difference (nodes : List ℚ)
    (hlen : 2 ≤ nodes.length) (hlast : node nodes (nodes.length-1) = 0) (y : ℝ) :
    (1-cos (2*π*y))*nodalPolynomial nodes y =
      node nodes 0-node nodes 1 +
      (∑ j ∈ Finset.Ico 1 (nodes.length-1),
        (2*node nodes j-node nodes (j-1)-node nodes (j+1))*cos (2*π*j*y)) -
      node nodes (nodes.length-2)*cos (2*π*(nodes.length-1:ℕ)*y) := by
  let C : ℕ → ℝ := fun j => cos (2*π*j*y)
  have h0 : C 0 = 1 := by simp [C]
  have hrec (k : ℕ) : C (k+2) = 2*C 1*C (k+1)-C k := by
    simpa [C, show ∀ j : ℕ, 2*π*j*y = (j:ℝ)*(2*π*y) by intro j; ring]
      using cos_nat_recurrence (2*π*y) k
  have h := second_difference_identity (node nodes) C h0 hrec (nodes.length-2)
  have hn : nodes.length-2+1 = nodes.length-1 := by omega
  have hnn : nodes.length-2+2 = (nodes.length-1)+1 := by omega
  rw [hn, hnn, Finset.sum_Ico_succ_top (by omega : 1 ≤ nodes.length-1),
    hlast, zero_mul, add_zero, mul_zero, zero_sub, zero_mul, sub_zero] at h
  simpa [nodalPolynomial, C, sub_eq_add_neg] using h

private theorem abs_mul_cos_le (a t : ℝ) : |a*cos t| ≤ |a| := by
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one t)

/-- The variation envelope retains cancellations before taking absolute values. -/
theorem nodalPolynomial_second_difference_bound (nodes : List ℚ)
    (hlen : 2 ≤ nodes.length) (hlast : node nodes (nodes.length-1) = 0) (y : ℝ) :
    |(1-cos (2*π*y))*nodalPolynomial nodes y| ≤
      |node nodes 1-node nodes 0| +
        (∑ j ∈ Finset.Ico 1 (nodes.length-1),
          |node nodes (j+1)-2*node nodes j+node nodes (j-1)|) +
        |node nodes (nodes.length-1)-node nodes (nodes.length-2)| := by
  rw [nodalPolynomial_second_difference nodes hlen hlast]
  apply (abs_sub _ _).trans
  apply add_le_add
  · apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_sub_comm]
    · apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      apply (abs_mul_cos_le _ _).trans
      rw [show 2*node nodes j-node nodes (j-1)-node nodes (j+1) =
        -(node nodes (j+1)-2*node nodes j+node nodes (j-1)) by ring, abs_neg]
  · rw [hlast, zero_sub, abs_neg]
    exact abs_mul_cos_le _ _

theorem inverseCosine_affineSpectrum_variation_bound (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (u : ℝ) (hu : u ≠ 0) :
    |inverseCosine (affineSpectrum nodes m) u| ≤ nodalV1 nodes m/(4*π^2*u^2) := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hq : 2*π*u/(m:ℝ) ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hu) hm'.ne'
  rw [inverseCosine_affineSpectrum nodes m hm, integral_hat_mul_cos _ hq]
  have heq : (1/(m:ℝ))*(2*(1-cos (2*π*u/(m:ℝ)))/(2*π*u/(m:ℝ))^2)*nodalPolynomial nodes (u/(m:ℝ)) =
      ((m:ℝ)/(2*π^2*u^2))*((1-cos (2*π*(u/(m:ℝ))))*nodalPolynomial nodes (u/(m:ℝ))) := by
    field_simp
    <;> ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)/(2*π^2*u^2))]
  apply (mul_le_mul_of_nonneg_left (nodalPolynomial_second_difference_bound nodes hlen hlast (u/(m:ℝ)))
    (by positivity : 0 ≤ (m:ℝ)/(2*π^2*u^2))).trans
  unfold nodalV1
  apply le_of_eq
  field_simp
  <;> ring

end RH080Next.Explicit
