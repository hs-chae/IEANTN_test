/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.AnalyticTransition

/-! Width applicability for the unchanged integer logarithm algorithm. These
kernel arithmetic proofs are inputs to the separate actual-source execution
refinement; by themselves they are not source-first PV. -/
namespace RamanujanPV.FiniteLogBounds
open Finset AnalyticTransition
set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev F : Nat := 2^60

theorem ceil_le_self (a : Nat) {b : Nat} (hb : 0 < b) : sourceCeilDiv a b ≤ a := by
  apply sourceCeilDiv_le hb
  nlinarith

theorem z_bound {num den : Nat} (hd : 0 < den) (half : 2*num ≤ den) :
    fixedLogZ num den ≤ 2^59 := by
  apply sourceCeilDiv_le hd
  norm_num
  nlinarith

theorem z2_bound {num den : Nat} (hd : 0 < den) (half : 2*num ≤ den) :
    fixedLogZ2 num den ≤ 2^59 := by
  have z := z_bound hd half
  apply sourceCeilDiv_le (by norm_num : 0 < (2^60 : Nat))
  nlinarith

theorem power_bound {z z2 : Nat} (hz : z ≤ 2^59) (hz2 : z2 ≤ 2^59) (k : Nat) :
    log20Power F z z2 k ≤ 2^59 := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    apply sourceCeilDiv_le (by norm_num : 0 < F)
    have product := Nat.mul_le_mul ih (hz2.trans (by norm_num : 2^59 ≤ F))
    simpa using product

theorem term_bound {z z2 : Nat} (hz : z ≤ 2^59) (hz2 : z2 ≤ 2^59) (k : Nat) :
    sourceCeilDiv (log20Power F z z2 k) (2*k+1) ≤ 2^59 :=
  (ceil_le_self _ (by omega)).trans (power_bound hz hz2 k)

theorem term_later_bound {z z2 k : Nat} (hz : z ≤ 2^59) (hz2 : z2 ≤ 2^59) (hk : 0 < k) :
    sourceCeilDiv (log20Power F z z2 k) (2*k+1) ≤ 2^58 := by
  apply sourceCeilDiv_le (by omega)
  have hp := power_bound hz hz2 k
  norm_num at hp ⊢
  nlinarith

theorem prefix_sum_bound {z z2 : Nat} (hz : z ≤ 2^59) (hz2 : z2 ≤ 2^59) (count : Nat) :
    (∑k∈range count,sourceCeilDiv (log20Power F z z2 k) (2*k+1)) ≤ count*F := by
  calc
    _ ≤ ∑_k∈range count,F := by
      apply sum_le_sum
      intro k hk
      exact (term_bound hz hz2 k).trans (by norm_num : 2^59 ≤ F)
    _ = count*F := by simp [Nat.mul_comm]

/-- The stronger bound also validates the original uint64 narrowing: unlike
the coarse20F estimate, this remains below2^64 after doubling and adding tail. -/
theorem sum_bound {z z2 : Nat} (hz : z ≤ 2^59) (hz2 : z2 ≤ 2^59) :
    log20Sum F z z2 ≤ 21*2^58 := by
  calc
    _ ≤ ∑k∈range 20,(2^58 + if k=0 then 2^58 else 0) := by
      apply sum_le_sum
      intro k hk
      by_cases zero : k=0
      · subst k
        have h := term_bound hz hz2 0
        norm_num at h ⊢
        exact h
      · simpa [zero] using term_later_bound hz hz2 (Nat.pos_of_ne_zero zero)
    _ = 21*2^58 := by norm_num [sum_add_distrib]

theorem tail_denominator {z2 : Nat} (hz2 : z2 ≤ 2^59) :
    F ≤ 41*(F-z2) ∧ 0 < 41*(F-z2) := by
  norm_num at hz2 ⊢
  omega

theorem tail_bound {z z2 : Nat} (hz : z ≤ 2^59) (hz2 : z2 ≤ 2^59) :
    sourceCeilDiv (2*log20Power F z z2 20*F) (41*(F-z2)) ≤ 2*F := by
  have hp := (power_bound hz hz2 20).trans (by norm_num : 2^59 ≤ F)
  have hd := tail_denominator hz2
  apply sourceCeilDiv_le hd.2
  calc
    2*log20Power F z z2 20*F ≤ 2*F*F := by nlinarith
    _ ≤ (2*F)*(41*(F-z2)) := Nat.mul_le_mul_left _ hd.1

theorem output_bound {z z2 : Nat} (hz : z ≤ 2^59) (hz2 : z2 ≤ 2^59) :
    log20Output F z z2 ≤ 13*F := by
  have hs := sum_bound hz hz2
  have ht := tail_bound hz hz2
  unfold log20Output
  norm_num [F] at hs ht ⊢
  omega

theorem fixed_series_bound {num den : Nat} (hd : 0 < den) (half : 2*num ≤ den) :
    fixedLogSeries num den ≤ 13*F :=
  output_bound (z_bound hd half) (z2_bound hd half)

theorem fixed_series_u64 {num den : Nat} (hd : 0 < den) (half : 2*num ≤ den) :
    fixedLogSeries num den < 2^64 := by
  have bound := fixed_series_bound hd half
  norm_num [F] at bound ⊢
  omega

/-- All original128-bit multiplicative expressions, with their exact operation
order. The numerical domains are sufficient for every original logarithm call. -/
theorem wide_products {num den : Nat} (hd : 0 < den) (half : 2*num ≤ den)
    (numBound : num ≤ 2000000000000) :
    F*num < 2^128 ∧
    (fixedLogZ num den)^2 < 2^128 ∧
    (∀k,log20Power F (fixedLogZ num den) (fixedLogZ2 num den) k * fixedLogZ2 num den < 2^128) ∧
    2*log20Power F (fixedLogZ num den) (fixedLogZ2 num den) 20*F < 2^128 ∧
    41*(F-fixedLogZ2 num den) < 2^128 ∧
    2*log20Sum F (fixedLogZ num den) (fixedLogZ2 num den) < 2^128 ∧
    log20Output F (fixedLogZ num den) (fixedLogZ2 num den) < 2^64 := by
  have hz := z_bound hd half
  have hz2 := z2_bound hd half
  have hs := sum_bound hz hz2
  have ho := output_bound hz hz2
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · norm_num [F] at numBound ⊢; nlinarith
  · norm_num at hz ⊢; nlinarith
  · intro k
    have hp := power_bound hz hz2 k
    have hm := Nat.mul_le_mul hp hz2
    norm_num at hm ⊢
    omega
  · have hp := power_bound hz hz2 20
    norm_num [F] at hp ⊢
    nlinarith
  · have h : F-fixedLogZ2 num den ≤ F := Nat.sub_le _ _
    norm_num [F] at h ⊢
    omega
  · norm_num [F] at hs ⊢; omega
  · norm_num [F] at ho ⊢; omega

theorem binary_input_domains {n two : Nat} (hn : 2 ≤ n) (upper : n ≤ 2000000000000)
    (low : two ≤ n) (high : n < 2*two) :
    0 < n+two ∧ n+two ≤ 4000000000000 ∧ n-two ≤ 2000000000000 ∧
      2*(n-two) ≤ n+two := by omega

theorem binary_output_bound {n two k : Nat} (low : two ≤ n) (high : n < 2*two)
    (kBound : k ≤ 40) : binaryLogUpper n two k ≤ 533*2^40 := by
  have domains : 0 < n+two ∧ 2*(n-two) ≤ n+two := by omega
  have log2 := fixed_series_bound (num:=1) (den:=3) (by norm_num) (by norm_num)
  have mantissa := fixed_series_bound domains.1 domains.2
  apply sourceCeilDiv_le (by norm_num : 0 < (2^20 : Nat))
  have mulBound := Nat.mul_le_mul kBound log2
  norm_num [F] at mulBound mantissa ⊢
  omega

theorem binary_output_u64 {n two k : Nat} (low : two ≤ n) (high : n < 2*two)
    (kBound : k ≤ 40) : binaryLogUpper n two k < 2^64 := by
  have h := binary_output_bound low high kBound
  norm_num at h ⊢
  omega

theorem binary_numerator_u128 {n two k : Nat} (low : two ≤ n) (high : n < 2*two)
    (kBound : k ≤ 40) :
    k*fixedLogSeries 1 3 + fixedLogSeries (n-two) (n+two) < 2^128 := by
  have domains : 0 < n+two ∧ 2*(n-two) ≤ n+two := by omega
  have log2 := fixed_series_bound (num:=1) (den:=3) (by norm_num) (by norm_num)
  have mantissa := fixed_series_bound domains.1 domains.2
  have mulBound := Nat.mul_le_mul kBound log2
  norm_num [F] at mulBound mantissa ⊢
  omega

#print axioms fixed_series_u64
#print axioms wide_products
#print axioms binary_output_u64
end RamanujanPV.FiniteLogBounds
