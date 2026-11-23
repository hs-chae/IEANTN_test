import Mathlib

/-! Kernel polynomial work for the frozen degree20 main term.
The finite coefficient argument follows the later own-arm1800s
CoefficientPV.poly_lower proof pattern, used only as post-lock verification.
No C source-execution or PV conclusion is claimed here. -/
namespace Ramanujan640.Polynomial
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def lhs (j : ℕ) : ℕ := ∑ i ∈ range (j+1), i.factorial*j.choose i
def rhs (j : ℕ) : ℕ := ∑ i ∈ range (j+1), i.factorial*(j-i).factorial
def coeff (j : ℕ) : ℕ := lhs j-rhs j
noncomputable def P (u : ℝ) : ℝ := ∑ k ∈ range 21, (k.factorial:ℝ)*u^k
noncomputable def Q (u : ℝ) : ℝ := ∑ j ∈ range 21, (lhs j:ℝ)*u^j
noncomputable def first (u : ℝ) : ℝ :=
  ∑ k ∈ range 21, (k.factorial:ℝ)*u^k/(1-u)^(k+1)
def tailCoeff (j : ℕ) : ℕ :=
  ∑ i ∈ range (20-j), (i+j+1).factorial*(20-i).factorial
noncomputable def tailNorm (u : ℝ) : ℝ :=
  ∑ j ∈ range 20, (tailCoeff j:ℝ)*u^(j+17)
noncomputable def difference (u : ℝ) : ℝ :=
  ∑ j ∈ range 21, ((lhs j:ℝ)-(rhs j:ℝ))*u^j

lemma coefficient_order (j : Fin 21) : rhs j ≤ lhs j := by
  revert j
  decide +kernel

lemma desc_coefficient (j : Fin 21) :
    (∑ k ∈ range 21, j.val.descFactorial k) = lhs j := by
  revert j
  decide +kernel

theorem difference_lower (u : ℝ) (hu : 0 ≤ u) :
    u^4+14*u^5+145*u^6+1412*u^7 ≤ difference u := by
  have hc (j : ℕ) (hj : j < 21) :
      (coeff j:ℝ) = (lhs j:ℝ)-(rhs j:ℝ) :=
    Nat.cast_sub (coefficient_order ⟨j,hj⟩)
  have hh : difference u = ∑ j ∈ range 21, (coeff j:ℝ)*u^j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hc j (Finset.mem_range.mp hj)]
  rw [hh]
  have hsplit : ∑ j ∈ range 8, (coeff j:ℝ)*u^j ≤
      ∑ j ∈ range 21, (coeff j:ℝ)*u^j := by
    have hsubset : range 8 ⊆ range 21 := by
      intro j hj
      exact Finset.mem_range.mpr (by have h := Finset.mem_range.mp hj; omega)
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j hj ht
    positivity
  convert! hsplit using 1
  norm_num [coeff,lhs,rhs,Finset.sum_range_succ,Nat.factorial,Nat.choose]

/-- Positivity truncation of the actual geometric-binomial series. -/
theorem first_truncation {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) : Q u ≤ first u := by
  have hn : ‖u‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hu] using hu1
  have hr (k : ℕ) :
      (∑ n ∈ range 21, (n.descFactorial k:ℝ)*u^n) ≤
        (k.factorial:ℝ)*u^k/(1-u)^(k+1) := by
    have h := hasSum_descFactorial_mul_geometric_of_norm_lt_one k hn
    have hs := Summable.sum_le_tsum (range 21)
      (fun n hn => by positivity : ∀ n ∉ range 21, 0 ≤ (n.descFactorial k:ℝ)*u^n)
      h.summable
    rw [h.tsum_eq] at hs
    exact hs
  have hsum := Finset.sum_le_sum (s:=range 21) (fun k hk => hr k)
  change (∑ k ∈ range 21, ∑ n ∈ range 21, (n.descFactorial k:ℝ)*u^n) ≤ first u at hsum
  rw [Finset.sum_comm] at hsum
  have heq : (∑ n ∈ range 21, ∑ k ∈ range 21, (n.descFactorial k:ℝ)*u^n) = Q u := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Finset.sum_mul,← Nat.cast_sum,desc_coefficient ⟨n,Finset.mem_range.mp hn⟩]
  rw [heq] at hsum
  exact hsum

/-- Exact square convolution, with the frozen degree21..40 discarded tail. -/
theorem square_identity (u : ℝ) :
    Q u-(P u)^2 = difference u-u^4*tailNorm u := by
  norm_num [Q,P,difference,lhs,rhs,tailNorm,tailCoeff,Finset.sum_range_succ,Nat.factorial]
  ring

theorem tail_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : tailNorm u ≤ tailNorm v := by
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv _) (by positivity)

theorem base_polynomial_lower {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    u^4+14*u^5+145*u^6+1412*u^7-u^4*tailNorm u ≤ first u-(P u)^2 := by
  have h := first_truncation hu hu1
  have hp := difference_lower u hu
  have he := square_identity u
  linarith

#print axioms coefficient_order
#print axioms difference_lower
#print axioms first_truncation
#print axioms square_identity
#print axioms base_polynomial_lower
end Ramanujan640.Polynomial
