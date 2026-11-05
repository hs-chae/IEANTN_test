/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Criterion
import Mathlib.Tactic.NormNum.Prime

/-!
# Prime ladders: small `x` by a finite, kernel-checked certificate

A ladder for `c = num/den` is a list `p₀ < p₁ < ⋯ < p_m` of numbers, all primes except possibly
`p₀`, with `(p_{i+1} - p_i)^8·den^8 ≤ num^8·p_i^7` at every step. The step condition is an exact
integer inequality, decided by the kernel. It says `p_{i+1} ≤ p_i + c·p_i^{7/8}`, so for every real
`x ∈ [p_i, p_{i+1})` the prime `p_{i+1}` lies in `(x, x + c·x^{7/8}]` (`ladder_sound`).
-/

namespace QRHGlobal

open Real IEANTN

/-- The step condition of a ladder for `c = num/den`, checked by evaluation. -/
def ladderOK (num den : ℕ) : List ℕ → Bool
  | p :: q :: rest =>
      (decide (p < q) && decide ((q - p) ^ 8 * den ^ 8 ≤ num ^ 8 * p ^ 7)) &&
        ladderOK num den (q :: rest)
  | _ => true

theorem rpow_seven_eighths_pow_eight {p : ℝ} (hp : 0 ≤ p) :
    (p ^ ((7 : ℝ) / 8)) ^ 8 = p ^ 7 := by
  rw [← rpow_natCast, ← rpow_mul hp]
  norm_num

/-- One rung: the exact step condition gives `q ≤ p + (num/den)·p^{7/8}`. -/
theorem step_le {num den p q : ℕ} (hden : 0 < den) (hpq : p < q)
    (h : (q - p) ^ 8 * den ^ 8 ≤ num ^ 8 * p ^ 7) :
    (q : ℝ) ≤ p + (num / den : ℝ) * (p : ℝ) ^ ((7 : ℝ) / 8) := by
  have hden0 : (0 : ℝ) < den := by exact_mod_cast hden
  have hd : (0 : ℝ) ≤ (q : ℝ) - p := by
    have : (p : ℝ) < q := by exact_mod_cast hpq
    linarith
  have ha : (0 : ℝ) ≤ (num / den : ℝ) * (p : ℝ) ^ ((7 : ℝ) / 8) := by positivity
  have hcast : ((q - p : ℕ) : ℝ) = (q : ℝ) - p := by
    rw [Nat.cast_sub hpq.le]
  have hR : ((q : ℝ) - p) ^ 8 * (den : ℝ) ^ 8 ≤ (num : ℝ) ^ 8 * (p : ℝ) ^ 7 := by
    rw [← hcast]
    exact_mod_cast h
  have h8 : ((q : ℝ) - p) ^ 8 ≤ ((num / den : ℝ) * (p : ℝ) ^ ((7 : ℝ) / 8)) ^ 8 := by
    rw [mul_pow, rpow_seven_eighths_pow_eight (Nat.cast_nonneg p), div_pow]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact hR
  have := (pow_le_pow_iff_left₀ hd ha (by norm_num : (8 : ℕ) ≠ 0)).mp h8
  linarith

theorem ladder_sound (num den : ℕ) (hden : 0 < den) :
    ∀ (p : ℕ) (rest : List ℕ), (∀ q ∈ rest, q.Prime) → ladderOK num den (p :: rest) = true →
      ∀ x : ℝ, (p : ℝ) ≤ x → x < (((p :: rest).getLast (List.cons_ne_nil _ _) : ℕ) : ℝ) →
        HasPrimeInInterval x ((num / den : ℝ) * x ^ ((7 : ℝ) / 8))
  | p, [], _, _, x, h1, h2 => by
      simp only [List.getLast_singleton] at h2
      linarith
  | p, q :: rest, hprime, hok, x, h1, h2 => by
      simp only [ladderOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨hpq, hstep⟩, hrest⟩ := hok
      by_cases hx : x < q
      · refine ⟨q, hprime q (by simp), hx, ?_⟩
        have hle := step_le hden hpq hstep
        have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        have hmono : (p : ℝ) ^ ((7 : ℝ) / 8) ≤ x ^ ((7 : ℝ) / 8) :=
          rpow_le_rpow hp0 h1 (by norm_num)
        have hc : (0 : ℝ) ≤ (num / den : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hmono hc]
      · replace hx := not_lt.mp hx
        have hlast : ((p :: q :: rest).getLast (List.cons_ne_nil _ _)) =
            ((q :: rest).getLast (List.cons_ne_nil _ _)) := List.getLast_cons _
        rw [hlast] at h2
        exact ladder_sound num den hden q rest (fun r hr ↦ hprime r (by simp [hr])) hrest x hx h2

end QRHGlobal
