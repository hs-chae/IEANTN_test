/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib

/-! Reuse of the pinned Mathlib Lucas/Pratt theorem and fast modular-power proof
machinery. These are ordinary kernel primality certificates, not PV by themselves. -/
namespace RamanujanPV.LocalLucas
set_option autoImplicit false
set_option maxHeartbeats 2000000

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

/-- Actual first prime after the previously certified55 composite steps. -/
theorem first_next_prime : Nat.Prime 38358837739 := by
  apply prime_of_factorization 38358837739 3 [2,3,3,3,3,13,151,120623]
  · decide +kernel
  · intro q hq
    simp only [List.mem_cons,List.mem_singleton] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · reduce_mod_char <;> norm_num
  · intro q hq
    simp only [List.mem_cons,List.mem_singleton] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> reduce_mod_char <;> norm_num

#print axioms first_next_prime
#print axioms prime_of_factorization
end RamanujanPV.LocalLucas
