/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import MertensProfile
namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set

/-- Reserve the omitted third power before using the geometric tail upper bound. -/
theorem geometric_finite_tail_plus_cube {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : Finset ℕ) (hs : ∀ k ∈ s, 2 ≤ k) (h3 : 3 ∉ s) :
    (∑ k ∈ s, r^k) + r^3 ≤ r^2/(1-r) := by
  have h := geometric_finite_tail hr0 hr1 (insert 3 s) (by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · norm_num
    · exact hs k hk)
  rw [Finset.sum_insert h3] at h
  linarith

theorem prime_finite_tail_plus_cube {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ k ∈ s, 2 ≤ k) (h3 : 3 ∉ s) :
    (∑ k ∈ s, Real.log p/(p:ℝ)^k) + Real.log p/(p:ℝ)^3 ≤ q p := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < p := by linarith
  have hg := geometric_finite_tail_plus_cube (r := (p:ℝ)⁻¹) (by positivity)
    (by simpa using (inv_lt_one₀ hp0).mpr hp1) s hs h3
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hm := mul_le_mul_of_nonneg_left hg hlog
  have hid : ((p:ℝ)⁻¹)^2/(1-(p:ℝ)⁻¹) = 1/((p:ℝ)*(p-1:ℝ)) := by
    field_simp [ne_of_gt hp0, ne_of_gt (by linarith : 0 < (p:ℝ)-1)]
  rw [hid] at hm
  simpa only [Finset.mul_sum, mul_add, div_eq_mul_inv, inv_pow,
    q, if_pos hp, one_mul] using hm

/-- Exact regrouping by prime base keeps the exponent set visible. -/
theorem finite_correction_by_base {x : ℝ} (hx : 2 ≤ x) :
    CA x - A x = ∑ p ∈ primes (Real.sqrt x),
      ∑ k ∈ (Finset.Ioc 1 (⌊Real.log x / Real.log 2⌋₊+1)).filter
        (fun (k : ℕ) => p ∈ primes (x^((1:ℝ)/k))), Real.log p/(p:ℝ)^k := by
  let N := ⌊Real.log x/Real.log 2⌋₊+1
  let P := primes (Real.sqrt x)
  have hexp := CA_prime_power_expansion (x := x) (N := N) (by linarith)
    (Nat.le_succ _)
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (by dsimp [N]; omega : 1 ≤ N)] at hexp
  have hbase : (∑ p ∈ primes (x^((1:ℝ)/(1:ℕ))), Real.log p/(p:ℝ)^(1:ℕ)) = A x := by
    simp [A]
  rw [hbase] at hexp
  have hsub : ∀ k ∈ Finset.Ioc 1 N, primes (x^((1:ℝ)/k)) ⊆ P := by
    intro k hk p hp
    have hk2 : (2:ℝ) ≤ k := by
      have hk' : 2 ≤ k := by have := (Finset.mem_Ioc.mp hk).1; omega
      exact_mod_cast hk'
    have he : (1:ℝ)/k ≤ 1/2 :=
      one_div_le_one_div_of_le (by norm_num) hk2
    have hr : x^((1:ℝ)/k) ≤ Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) he
    rcases Finset.mem_filter.mp hp with ⟨hpr,hpP⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hpr).1,
      le_trans (Finset.mem_Ioc.mp hpr).2 (Nat.floor_le_floor hr)⟩,hpP⟩
  have hr : (∑ k ∈ Finset.Ioc 1 N, ∑ p ∈ primes (x^((1:ℝ)/k)),
      Real.log p/(p:ℝ)^k) = ∑ p ∈ P,
      ∑ k ∈ (Finset.Ioc 1 N).filter
        (fun (k : ℕ) => p ∈ primes (x^((1:ℝ)/k))), Real.log p/(p:ℝ)^k := by
    calc _ = ∑ k ∈ Finset.Ioc 1 N, ∑ p ∈ P,
        if p ∈ primes (x^((1:ℝ)/k)) then Real.log p/(p:ℝ)^k else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          have hs := Finset.sum_subset (hsub k hk)
            (f := fun p => if p ∈ primes (x^((1:ℝ)/k))
              then Real.log p/(p:ℝ)^k else 0) (by
                intro p hp hnot
                simp only [if_neg hnot])
          simpa only [Finset.sum_ite_mem, Finset.inter_self] using hs
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.sum_filter]
  dsimp [N,P] at hexp hr
  linarith

/-- Recover every explicitly omitted cube in a finite prime collection. -/
theorem finite_correction_reserves_cubes {x : ℝ} (hx : 2 ≤ x)
    (mid : Finset ℕ) (hsub : mid ⊆ primes (Real.sqrt x))
    (hcube : ∀ p ∈ mid, x < (p:ℝ)^3) :
    CA x - A x + ∑ p ∈ mid, Real.log p/(p:ℝ)^3 ≤
      ∑ p ∈ primes (Real.sqrt x), q p := by
  let P := primes (Real.sqrt x)
  let N := ⌊Real.log x/Real.log 2⌋₊+1
  let powers := fun p => (Finset.Ioc 1 N).filter
    (fun (k : ℕ) => p ∈ primes (x^((1:ℝ)/k)))
  have hmid : (∑ p ∈ mid, Real.log p/(p:ℝ)^3) =
      ∑ p ∈ P, if p ∈ mid then Real.log p/(p:ℝ)^3 else 0 := by
    have hs := Finset.sum_subset hsub
      (f := fun p => if p ∈ mid then Real.log p/(p:ℝ)^3 else 0) (by
        intro p hp hnot
        simp only [if_neg hnot])
    simpa only [Finset.sum_ite_mem, Finset.inter_self] using hs
  rw [finite_correction_by_base hx,hmid,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hpP : p.Prime := (Finset.mem_filter.mp hp).2
  have hs : ∀ k ∈ powers p, 2 ≤ k := by
    intro k hk
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1).1
    omega
  by_cases hpm : p ∈ mid
  · have h3 : 3 ∉ powers p := by
      intro hmem
      have hpr := (Finset.mem_filter.mp hmem).2
      have hnat := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpr).1).2
      have hpp : (p:ℝ) ≤ x^((1:ℝ)/3) :=
        le_trans (Nat.cast_le.mpr hnat) (Nat.floor_le (by positivity))
      have hpp3 : (p:ℝ)^3 ≤ x := by
        have hh := (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg p)
          (by linarith : 0 ≤ x) (by norm_num : (0:ℝ)<3)).mp (by simpa using hpp)
        norm_num at hh
        exact hh
      linarith [hcube p hpm]
    simpa only [if_pos hpm] using prime_finite_tail_plus_cube hpP (powers p) hs h3
  · simpa only [if_neg hpm,add_zero] using prime_finite_tail hpP (powers p) hs

/-- fullTail includes both all square-prime tail terms and the newly recovered
middle-prime cube terms. Neither correction is assumed numerically. -/
theorem fullTail_ge_square_add_cubes {x M : ℝ} (hx : 2 ≤ x)
    (mid : Finset ℕ) (hsub : mid ⊆ primes (Real.sqrt x))
    (hcube : ∀ p ∈ mid, x < (p:ℝ)^3) :
    squareFinite (Real.sqrt x) M + (∑ p ∈ mid, Real.log p/(p:ℝ)^3) ≤ fullTail x := by
  let lo := primes (Real.sqrt x)
  let hi := (Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊M⌋₊).filter Nat.Prime
  have hd : Disjoint lo hi := by
    apply Finset.disjoint_left.mpr
    intro n hnlo hnhi
    have h1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hnlo).1).2
    have h2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hnhi).1).1
    omega
  have hs := correction_summable.sum_le_tsum (lo ∪ hi) (fun n _ => q_nonneg n)
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
  have hc := finite_correction_reserves_cubes hx mid hsub hcube
  unfold fullTail correctionConstant
  dsimp [lo] at hs hc
  linarith

#print axioms fullTail_ge_square_add_cubes
end MertensPositive
