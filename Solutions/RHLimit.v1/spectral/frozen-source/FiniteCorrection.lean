/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Definitions
namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set

/-- Finite geometric tails, with no numerical evaluation or infinite prime table. -/
theorem geometric_finite_tail {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : Finset ℕ) (hs : ∀ k ∈ s, 2 ≤ k) :
    ∑ k ∈ s, r ^ k ≤ r ^ 2 / (1 - r) := by
  have hsum := summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr0])
  have hd : Disjoint s ({0, 1} : Finset ℕ) := by
    apply Finset.disjoint_left.mpr
    intro k hk hki
    have hh := hs k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hki
    omega
  have hb := hsum.sum_le_tsum (s ∪ {0, 1}) (fun k _ => pow_nonneg hr0 k)
  rw [Finset.sum_union hd] at hb
  simp only [Finset.sum_insert (by simp : (0:ℕ) ∉ ({1}:Finset ℕ)),
    Finset.sum_singleton, pow_zero, pow_one] at hb
  rw [tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr0])] at hb
  have hid : r^2 / (1-r) = (1-r)⁻¹ - 1 - r := by
    field_simp [ne_of_gt (by linarith : 0 < 1-r)]
    <;> ring
  rw [hid]
  linarith

/-- A finite collection of powers k≥2 of a single prime contributes at most its full
geometric correction log(p)/(p(p−1)). -/
theorem prime_finite_tail {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ k ∈ s, 2 ≤ k) :
    ∑ k ∈ s, Real.log p / (p : ℝ)^k ≤ q p := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < p := by linarith
  have hgeo := geometric_finite_tail (r := (p:ℝ)⁻¹) (by positivity)
    (by simpa using (inv_lt_one₀ hp0).mpr hp1) s hs
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hsum : (∑ k ∈ s, Real.log p / (p:ℝ)^k) =
      Real.log p * ∑ k ∈ s, ((p:ℝ)⁻¹)^k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [inv_pow, div_eq_mul_inv]
  rw [hsum]
  have hid : ((p:ℝ)⁻¹)^2 / (1-(p:ℝ)⁻¹) = 1/((p:ℝ)*(p-1:ℝ)) := by
    field_simp [ne_of_gt hp0, ne_of_gt (by linarith : 0 < (p:ℝ)-1)]
    <;> ring
  calc Real.log p * ∑ k ∈ s, ((p:ℝ)⁻¹)^k ≤
      Real.log p * (((p:ℝ)⁻¹)^2/(1-(p:ℝ)⁻¹)) := mul_le_mul_of_nonneg_left hgeo hlog
    _ = q p := by rw [hid]; simp [q, hp, div_eq_mul_inv]

/-- Mathlib's actual finite prime-power bijection, applied to weighted von Mangoldt. -/
theorem CA_prime_power_expansion {x : ℝ} (hx : 0 ≤ x) {N : ℕ}
    (hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    CA x = ∑ k ∈ Finset.Icc 1 N,
      ∑ p ∈ primes (x ^ ((1:ℝ)/k)), Real.log p / (p:ℝ)^k := by
  have hfilter : CA x = ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter IsPrimePow,
      (vonMangoldt n:ℝ)/n := by
    unfold CA
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs with h
    · rfl
    · simp [vonMangoldt_eq_zero_iff.mpr h]
  rw [hfilter, Chebyshev.sum_PrimePow_eq_sum_sum' _ hx hN]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  have hpP : p.Prime := (Finset.mem_filter.mp hp).2
  have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  rw [vonMangoldt_apply_pow hk0, vonMangoldt_apply_prime hpP, Nat.cast_pow]

/-- The finite nonsquare-free correction only uses prime bases at most sqrt(x). -/
theorem finite_correction_upper {x : ℝ} (hx : 2 ≤ x) :
    CA x - A x ≤ ∑ p ∈ primes (Real.sqrt x), q p := by
  let N := ⌊Real.log x / Real.log 2⌋₊ + 1
  have hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N := Nat.le_succ _
  have hN1 : 1 ≤ N := by omega
  have hexp := CA_prime_power_expansion (by linarith : 0 ≤ x) hN
  rw [← Finset.add_sum_Ioc_eq_sum_Icc hN1] at hexp
  have hbase : (∑ p ∈ primes (x ^ ((1:ℝ)/(1:ℕ))), Real.log p / (p:ℝ)^(1:ℕ)) = A x := by
    simp [A]
  rw [hbase] at hexp
  have hmono : ∀ k ∈ Finset.Ioc 1 N,
      (∑ p ∈ primes (x ^ ((1:ℝ)/k)), Real.log p / (p:ℝ)^k) ≤
      ∑ p ∈ primes (Real.sqrt x), Real.log p / (p:ℝ)^k := by
    intro k hk
    have hk2 : 2 ≤ k := by have := (Finset.mem_Ioc.mp hk).1; omega
    have hkr : (2:ℝ) ≤ k := by exact_mod_cast hk2
    have he : (1:ℝ)/k ≤ 1/2 := by apply one_div_le_one_div_of_le (by norm_num) hkr
    have hr : x ^ ((1:ℝ)/k) ≤ Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) he
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpr,hpP⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hpr).1,
        le_trans (Finset.mem_Ioc.mp hpr).2 (Nat.floor_le_floor hr)⟩,hpP⟩
    · intro p hp hnot
      have hpP := (Finset.mem_filter.mp hp).2
      have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hpP.one_le
      exact div_nonneg (Real.log_nonneg hp1) (by positivity)
  have hb : (∑ k ∈ Finset.Ioc 1 N, ∑ p ∈ primes (x ^ ((1:ℝ)/k)),
      Real.log p / (p:ℝ)^k) ≤ ∑ p ∈ primes (Real.sqrt x), q p := by
    calc _ ≤ ∑ k ∈ Finset.Ioc 1 N, ∑ p ∈ primes (Real.sqrt x),
        Real.log p / (p:ℝ)^k := Finset.sum_le_sum hmono
      _ = ∑ p ∈ primes (Real.sqrt x), ∑ k ∈ Finset.Ioc 1 N,
          Real.log p / (p:ℝ)^k := Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun p hp =>
        prime_finite_tail (Finset.mem_filter.mp hp).2 _
          (fun k hk => by have := (Finset.mem_Ioc.mp hk).1; omega)
  linarith [hexp]
end MertensPositive

namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set
/-- The full correction constant includes every prime, including p>x. Its remaining tail
dominates any finite square-prime tail beyond sqrt(x). -/
theorem fullTail_ge_squareFinite (hS : PublishedCorrectionSummable) {x M : ℝ}
    (hx : 2 ≤ x) :
    squareFinite (Real.sqrt x) M ≤ fullTail x := by
  let lo := primes (Real.sqrt x)
  let hi := (Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊M⌋₊).filter Nat.Prime
  have hd : Disjoint lo hi := by
    apply Finset.disjoint_left.mpr
    intro n hnlo hnhi
    have h1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hnlo).1).2
    have h2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hnhi).1).1
    omega
  have hs := hS.sum_le_tsum (lo ∪ hi) (fun n _ => q_nonneg n)
  rw [Finset.sum_union hd] at hs
  have hsq : squareFinite (Real.sqrt x) M ≤ ∑ n ∈ hi,q n := by
    apply Finset.sum_le_sum
    intro n hn
    have hp : n.Prime := (Finset.mem_filter.mp hn).2
    have hp1 : (1:ℝ) < n := by exact_mod_cast hp.one_lt
    have hn0 : (0:ℝ) < n := by linarith
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    dsimp [q]
    rw [if_pos hp]
    apply div_le_div_of_nonneg_left hl (by positivity)
    nlinarith
  have hc := finite_correction_upper hx
  unfold fullTail correctionConstant
  dsimp [lo] at hs hc
  linarith
end MertensPositive
