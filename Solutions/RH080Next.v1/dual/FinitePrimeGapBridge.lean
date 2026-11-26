/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Real Set
namespace RH080Next.FiniteGap

/-- Literal CMS (2019), (1.15), citing Oliveira e Silva--Herzog--Pardi
Section2.2: strict squared-log gap for every lower prime11..4*10^18.
This historical finite computation is an explicit input, not new PV. -/
def HistoricalFiniteGap : Prop :=
  ∀ n : ℕ, 11 ≤ Nat.nth Nat.Prime n →
    Nat.nth Nat.Prime n ≤ 4 * 10 ^ 18 →
    (Nat.nth Nat.Prime (n+1) : ℝ) - Nat.nth Nat.Prime n <
      log (Nat.nth Nat.Prime n : ℝ) ^ 2

lemma log_le_two_sqrt_over_e (x : ℝ) (hx : 0 < x) :
    log x ≤ (2 / exp 1) * sqrt x := by
  have hs : 0 < sqrt x := sqrt_pos.2 hx
  have he : 0 < exp (1 : ℝ) := exp_pos _
  have h := log_le_sub_one_of_pos (div_pos hs he)
  rw [log_div hs.ne' he.ne', log_exp, log_sqrt hx.le] at h
  have h2 : log x ≤ 2 * (sqrt x / exp 1) := by linarith
  convert h2 using 1 <;> ring

lemma log_lt_074_sqrt (x : ℝ) (hx : 0 < x) :
    log x < (74/100 : ℝ) * sqrt x := by
  have he : 0 < exp (1 : ℝ) := exp_pos _
  have hc : (2 : ℝ) / exp 1 < 74/100 := by
    apply (div_lt_iff₀ he).2
    have h := exp_one_gt_d9
    linarith
  exact (log_le_two_sqrt_over_e x hx).trans_lt
    (mul_lt_mul_of_pos_right hc (sqrt_pos.2 hx))

lemma prime_bracketing (x : ℝ) (hx : 11 ≤ x) :
    ∃ n : ℕ, 11 ≤ Nat.nth Nat.Prime n ∧
      (Nat.nth Nat.Prime n : ℝ) ≤ x ∧ x < (Nat.nth Nat.Prime (n+1) : ℝ) := by
  have hp : (Set.ofPred Nat.Prime).Infinite := by
    exact fun h => Nat.not_bddAbove_setOfPred_prime h.bddAbove
  let k := Nat.floor x + 1
  let N := Nat.count Nat.Prime k
  have hfloor : 11 ≤ Nat.floor x := by exact Nat.le_floor hx
  have hcount : 5 ≤ N := by
    have h := Nat.count_monotone Nat.Prime (show 12 ≤ k by dsimp [k]; omega)
    have hsmall : Nat.count Nat.Prime 12 = 5 := by decide
    simpa only [hsmall] using h
  refine ⟨N-1, ?_, ?_, ?_⟩
  · have h := (Nat.nth_monotone hp) (show 4 ≤ N-1 by omega)
    simpa using h
  · have h := (Nat.lt_nth_iff_count_lt hp).1 (show N-1 < Nat.count Nat.Prime k by dsimp [N]; omega)
    have hh : Nat.nth Nat.Prime (N-1) ≤ Nat.floor x := by dsimp [k] at h; omega
    exact (Nat.cast_le.mpr hh).trans (Nat.floor_le (by linarith : 0 ≤ x))
  · have h := Nat.le_nth_count hp k
    have hN : N-1+1=N := by omega
    rw [hN]
    exact (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast h)

/-- A complete all-real finite bridge; the upper endpoint prime is strictly
inside the requested interval, rather than merely at its right boundary. -/
theorem historical_gap_implies_074 (hgap : HistoricalFiniteGap)
    (x : ℝ) (hx : 11 ≤ x) (hX : x ≤ 4 * 10 ^ 18) :
    ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ (p : ℝ) < x + (74/100 : ℝ)*sqrt x*log x := by
  obtain ⟨n, hp11, hpx, hxq⟩ := prime_bracketing x hx
  have hpX : Nat.nth Nat.Prime n ≤ 4*10^18 := by exact_mod_cast hpx.trans hX
  have hg := hgap n hp11 hpX
  have hp0 : (0 : ℝ) < Nat.nth Nat.Prime n := by exact_mod_cast (show 0 < Nat.nth Nat.Prime n by omega)
  have hlog : log (Nat.nth Nat.Prime n : ℝ) ≤ log x := log_le_log hp0 hpx
  have hlogp : 0 ≤ log (Nat.nth Nat.Prime n : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ Nat.nth Nat.Prime n by omega))
  have hlogx : 0 < log x := log_pos (by linarith)
  have hsq : log (Nat.nth Nat.Prime n : ℝ)^2 ≤ log x^2 := by nlinarith
  have hlast := mul_lt_mul_of_pos_right (log_lt_074_sqrt x (by linarith)) hlogx
  refine ⟨Nat.nth Nat.Prime (n+1), Nat.nth_mem_of_infinite ?_ _, hxq, ?_⟩
  · exact fun h => Nat.not_bddAbove_setOfPred_prime h.bddAbove
  · nlinarith

lemma log_seven_lower : (9729/5000 : ℝ) < log 7 := by
  have hc := le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 859/20000 by norm_num)
  norm_num at hc
  have hp : (20859/20000 : ℝ) ^ 8 ≤ 7/5 := by norm_num
  have hl := log_le_log (by norm_num : (0 : ℝ) < (20859/20000)^8) hp
  rw [log_pow, log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)] at hl
  have hf := log_five_gt_d9
  linarith

lemma width_0777_at_four : (2 : ℝ) < (777/1000 : ℝ)*sqrt 4*log 4 := by
  have hl : log (4 : ℝ) = 2*log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, log_pow]
    norm_num
  rw [hl]
  norm_num
  have h := log_two_gt_d9
  linarith

lemma width_0777_at_seven : (4 : ℝ) < (777/1000 : ℝ)*sqrt 7*log 7 := by
  have hs : (264575/100000 : ℝ) < sqrt 7 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 7), sqrt_nonneg (7 : ℝ)]
  have hl := mul_lt_mul_of_pos_left log_seven_lower
    (by positivity : (0 : ℝ) < (777/1000 : ℝ)*sqrt 7)
  nlinarith

lemma sqrt_log_mono (a x : ℝ) (ha : 1 ≤ a) (hx : a ≤ x) :
    sqrt a*log a ≤ sqrt x*log x := by
  exact mul_le_mul (sqrt_le_sqrt hx) (log_le_log (by linarith) hx)
    (log_nonneg ha) (sqrt_nonneg _)

/-- Direct kernel-proved small cases around4,5,7,11. The strict upper boundary
atx=7 is covered by the certified rational lower bound onlog7. -/
theorem direct_small_0777 (x : ℝ) (hx : 4 ≤ x) (h11 : x < 11) :
    ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ (p : ℝ) < x + (777/1000 : ℝ)*sqrt x*log x := by
  have h4 := mul_le_mul_of_nonneg_left (sqrt_log_mono 4 x (by norm_num) hx)
    (by norm_num : (0 : ℝ) ≤ 777/1000)
  have hwidth : 2 < (777/1000 : ℝ)*sqrt x*log x := by
    nlinarith [width_0777_at_four]
  by_cases h5 : x < 5
  · refine ⟨5, by decide, h5, ?_⟩
    norm_num
    linarith
  by_cases h7 : x < 7
  · refine ⟨7, by decide, h7, ?_⟩
    norm_num
    linarith
  have h7w := mul_le_mul_of_nonneg_left
    (sqrt_log_mono 7 x (by norm_num) (le_of_not_gt h7))
    (by norm_num : (0 : ℝ) ≤ 777/1000)
  refine ⟨11, by decide, h11, ?_⟩
  norm_num
  nlinarith [width_0777_at_seven]

/-- Uniform finite c=0.8 bridge up to the actual source cutoff. It consumes
CMS(1.15) directly, coversallrealx≥4 and keeps bothinterval endpointsopen. -/
theorem finite_open_08 (hgap : HistoricalFiniteGap) (x : ℝ)
    (hx : 4 ≤ x) (hX : x ≤ 4*10^18) :
    ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ (p : ℝ) < x + (8/10 : ℝ)*sqrt x*log x := by
  have hs : 0 < sqrt x*log x := mul_pos (sqrt_pos.2 (by linarith)) (log_pos (by linarith))
  by_cases h11 : x < 11
  · obtain ⟨p,hp,hlo,hhi⟩ := direct_small_0777 x hx h11
    exact ⟨p,hp,hlo,by nlinarith⟩
  · obtain ⟨p,hp,hlo,hhi⟩ := historical_gap_implies_074 hgap x (le_of_not_gt h11) hX
    exact ⟨p,hp,hlo,by nlinarith⟩

lemma exp42_lt_historical_cutoff : exp (42 : ℝ) < 4*10^18 := by
  have hi : exp (42 : ℝ) = exp 1 ^ 42 := by
    simpa using exp_nat_mul (1 : ℝ) 42
  have hp : exp (1 : ℝ)^42 ≤ (27182818286/10000000000 : ℝ)^42 := by
    gcongr
    have h := exp_one_lt_d9.le
    norm_num at h ⊢
    exact h
  rw [hi]
  exact hp.trans_lt (by norm_num)

/-- The complete finite bridge overlaps the analytic onsetexp42. -/
theorem finite_open_08_through_exp42 (hgap : HistoricalFiniteGap) (x : ℝ)
    (hx : 4 ≤ x) (hX : x ≤ exp 42) :
    ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ (p : ℝ) < x + (8/10 : ℝ)*sqrt x*log x :=
  finite_open_08 hgap x hx (hX.trans exp42_lt_historical_cutoff.le)

#print axioms historical_gap_implies_074
#print axioms direct_small_0777
#print axioms finite_open_08
#print axioms finite_open_08_through_exp42
end RH080Next.FiniteGap
