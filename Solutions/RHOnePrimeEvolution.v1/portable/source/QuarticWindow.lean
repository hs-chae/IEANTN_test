/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace QuarticWindow
open Real Finset

noncomputable def primeCounting (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊

noncomputable def primesBetween (a b : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊b⌋₊).filter fun p => a < (p : ℝ) ∧ (p : ℝ) < b

noncomputable def window (s : ℝ) : ℝ := max 0 (1 - s ^ 4)

noncomputable def primeWeight (L δ : ℝ) (p : ℕ) : ℝ :=
  window ((Real.log p - L) / δ) * (Real.log p / Real.sqrt p)

noncomputable def primeWeighted (a b L δ : ℝ) : ℝ :=
  ∑ p ∈ primesBetween a b, primeWeight L δ p

noncomputable def mangoldtWeighted (a b L δ : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range (⌊b⌋₊ + 1)).filter (fun n : ℕ => a < (n : ℝ) ∧ (n : ℝ) < b),
    window ((Real.log (n : ℝ) - L) / δ) *
      ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt (n : ℝ))

theorem window_nonneg (s : ℝ) : 0 ≤ window s := le_max_left _ _

theorem window_le_one (s : ℝ) : window s ≤ 1 := by
  unfold window
  exact max_le (by norm_num) (by nlinarith [sq_nonneg (s ^ 2)])

/-- This actual logarithmic prime weight decreases once `log a ≥ 2`. -/
theorem log_div_sqrt_antitone {a p : ℝ} (ha : 0 < a) (hap : a ≤ p)
    (hla : 2 ≤ Real.log a) : Real.log p / Real.sqrt p ≤ Real.log a / Real.sqrt a := by
  have hp : 0 < p := ha.trans_le hap
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hrat : 1 ≤ Real.sqrt p / Real.sqrt a :=
    (one_le_div hsa).mpr (Real.sqrt_le_sqrt hap)
  have hlograt : Real.log (Real.sqrt p / Real.sqrt a) =
      (Real.log p - Real.log a) / 2 := by
    rw [Real.log_div hsp.ne' hsa.ne', Real.log_sqrt hp.le, Real.log_sqrt ha.le]
    ring
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsp hsa)
  rw [hlograt] at hlog
  have hmul := mul_le_mul_of_nonneg_right hla (sub_nonneg.mpr hrat)
  apply (div_le_iff₀ hsp).mpr
  have hbound : Real.log p ≤ Real.log a * (Real.sqrt p / Real.sqrt a) := by
    nlinarith
  calc
    Real.log p ≤ Real.log a * (Real.sqrt p / Real.sqrt a) := hbound
    _ = Real.log a / Real.sqrt a * Real.sqrt p := by ring

/-- An actual finite prime-weight sum is bounded by the actual count. -/
theorem weighted_le_count {a b L δ : ℝ} (ha : 0 < a) (hla : 2 ≤ Real.log a) :
    primeWeighted a b L δ ≤
      ((primesBetween a b).card : ℝ) * (Real.log a / Real.sqrt a) := by
  unfold primeWeighted
  calc
    ∑ p ∈ primesBetween a b, primeWeight L δ p ≤
        ∑ _p ∈ primesBetween a b, Real.log a / Real.sqrt a := by
      apply Finset.sum_le_sum
      intro p hp
      have hmem := (Finset.mem_filter.mp hp).2
      have hpos : 0 < (p : ℝ) := ha.trans hmem.1
      have hlogp : 0 ≤ Real.log p :=
        (by linarith : 0 ≤ Real.log a).trans
          (Real.log_le_log ha hmem.1.le)
      unfold primeWeight
      calc
        window ((Real.log p - L) / δ) * (Real.log p / Real.sqrt p) ≤
            1 * (Real.log p / Real.sqrt p) :=
          mul_le_mul_of_nonneg_right (window_le_one _)
            (div_nonneg hlogp (Real.sqrt_nonneg _))
        _ ≤ Real.log a / Real.sqrt a := by
          simpa only [one_mul] using log_div_sqrt_antitone ha hmem.1.le hla
    _ = ((primesBetween a b).card : ℝ) * (Real.log a / Real.sqrt a) := by
      simp

/-- Strict open-window counts are bounded by the ordinary right-continuous difference. -/
theorem count_le_primeCounting_difference {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((primesBetween a b).card : ℝ) ≤ primeCounting b - primeCounting a := by
  classical
  let A := Nat.primesLE ⌊a⌋₊
  let B := primesBetween a b
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    have hpaf : (p : ℝ) ≤ (⌊a⌋₊ : ℝ) := by
      exact_mod_cast (Nat.mem_primesLE.mp hpA).1
    have hpa : (p : ℝ) ≤ a := hpaf.trans (Nat.floor_le ha)
    have hpb := (Finset.mem_filter.mp hpB).2.1
    exact (not_lt_of_ge hpa) hpb
  have hsub : A ∪ B ⊆ Nat.primesLE ⌊b⌋₊ := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have mem := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesLE.mpr ⟨mem.1.trans (Nat.floor_le_floor hab), mem.2⟩
    · exact (Finset.mem_filter.mp hp).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hcard
  have hreal : ((A.card : ℕ) : ℝ) + B.card ≤ (Nat.primesLE ⌊b⌋₊).card := by
    exact_mod_cast hcard
  dsimp [A, B] at hreal
  rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hreal
  unfold primeCounting
  linarith

/-- A non-circular consumer: the premise is the actual weighted prime sum. -/
theorem prime_count_from_weighted {a b L δ lam η : ℝ} (ha : 0 < a)
    (hla : 2 ≤ Real.log a) (hab : a ≤ b) (hL : L - δ = Real.log a)
    (hη : 0 < η) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hweighted : lam * L + η < primeWeighted a b L δ) :
    (lam + η / Real.log a) * Real.sqrt a < primeCounting b - primeCounting a := by
  have hlog : 0 < Real.log a := by linarith
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hbound := weighted_le_count (b := b) (L := L) (δ := δ) ha hla
  have hcard := count_le_primeCounting_difference ha.le hab
  have hstrict : lam * Real.log a + η <
      ((primesBetween a b).card : ℝ) * (Real.log a / Real.sqrt a) := by
    have : lam * Real.log a ≤ lam * L := mul_le_mul_of_nonneg_left (by linarith) hlam
    linarith
  have hcnt : (lam + η / Real.log a) * Real.sqrt a <
      ((primesBetween a b).card : ℝ) := by
    have ht := (div_lt_iff₀ (div_pos hlog hsa)).mpr hstrict
    have heq : (lam * Real.log a + η) / (Real.log a / Real.sqrt a) =
        (lam + η / Real.log a) * Real.sqrt a := by
      field_simp
      <;> ring
    rwa [heq] at ht
  exact hcnt.trans_le hcard

#print axioms prime_count_from_weighted
end QuarticWindow
