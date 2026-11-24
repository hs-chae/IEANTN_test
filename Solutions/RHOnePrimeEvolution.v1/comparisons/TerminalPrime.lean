/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic

/-! Ordinary Lucas kernel certificates; generic helper reused from the existing
LocalLucas module. No source-first PV or exhaustive gap verification is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536
namespace RHOnePrimeEvolution.FiniteEndpoint
lemma prime_mem_of_dvd_prod {q : Nat} (hq : Nat.Prime q) (factors : List Nat)
    (good : ∀ p ∈ factors, Nat.Prime p) (divides : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil => simp at divides; exact (hq.ne_one divides).elim
  | cons p ps ih =>
    have alt : q ∣ p ∨ q ∣ ps.prod := hq.dvd_mul.mp divides
    rcases alt with first|rest
    · have equal : q=p := ((Nat.dvd_prime (good p (by simp))).mp first).resolve_left hq.ne_one
      simp [equal]
    · exact List.mem_cons_of_mem p (ih (fun p hp=>good p (by simp [hp])) rest)

/-- Every prime factor of p−1 is covered by the checked complete product and
proved-prime factors; all required modular orders are explicitly established. -/
theorem prime_of_factorization (p a : Nat) (factors : List Nat)
    (product : factors.prod=p-1) (good : ∀ q ∈ factors, Nat.Prime q)
    (full : (a : ZMod p)^(p-1)=1)
    (proper : ∀ q ∈ factors, (a : ZMod p)^((p-1)/q) ≠ 1) : Nat.Prime p := by
  apply lucas_primality p (a : ZMod p) full
  intro q hq hdiv
  rw [←product] at hdiv
  exact proper q (prime_mem_of_dvd_prod hq factors good hdiv)


theorem prime_15331 : Nat.Prime 15331 := by
  apply prime_of_factorization 15331 2 [2,3,5,7,73]
  · decide +kernel
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · reduce_mod_char <;> norm_num
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> reduce_mod_char <;> norm_num <;> decide +kernel

theorem prime_5594472617641 : Nat.Prime 5594472617641 := by
  apply prime_of_factorization 5594472617641 13 [2,2,2,3,5,1427,2131,15331]
  · decide +kernel
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_15331
  · reduce_mod_char <;> norm_num
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> reduce_mod_char <;> norm_num <;> decide +kernel

theorem terminal_prime : Nat.Prime 18446744073709551557 := by
  apply prime_of_factorization 18446744073709551557 2 [2,2,11,137,547,5594472617641]
  · decide +kernel
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_5594472617641
  · reduce_mod_char <;> norm_num
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> reduce_mod_char <;> norm_num <;> decide +kernel

#print axioms terminal_prime
end RHOnePrimeEvolution.FiniteEndpoint
