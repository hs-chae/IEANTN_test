/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.AnalyticTransition
import Mathlib.Data.Nat.Log

/-! Mathematical accuracy strengthening for the unchanged C log program's exact
integer model. This file alone is kernel mathematics/certificate checking. The
actual C source, AST, width/loop execution and returned output are connected
separately in CLogSource. No lower log bound is created by an unproved subtraction.
-/
namespace CLogMathLower
open Real Finset RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def atanhQ (r : ℚ) : ℚ := ∑ k ∈ Finset.range 20, 2 * r ^ (2 * k + 1) / (2 * k + 1 : ℕ)
def lowerQ (n two k : ℕ) : ℚ :=
  (k : ℚ) * atanhQ (1 / 3) + atanhQ ((n - two : ℕ) / (n + two : ℕ))
def exponent (n : ℕ) : ℕ := Nat.log2 n
def two (n : ℕ) : ℕ := 2 ^ exponent n
def model (n : ℕ) : ℕ := binaryLogUpper n (two n) (exponent n)
def lowerCheck : Bool := (List.range 129).all fun n =>
  if n < 2 then true else decide
    ((model n : ℚ) / 2 ^ 40 - 1 / 2 ^ 30 ≤ lowerQ n (two n) (exponent n))

theorem normalization {n : ℕ} (hn : 2 ≤ n) : two n ≤ n ∧ n < 2 * two n := by
  have hn0 : n ≠ 0 := by omega
  have hl := Nat.pow_log_le_self 2 hn0
  have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  simpa [two, exponent, Nat.log2_eq_log_two, pow_succ, Nat.mul_comm] using And.intro hl hh

theorem atanhQ_cast (r : ℚ) : (atanhQ r : ℝ) = logAtanhPoly 20 (r : ℝ) := by
  unfold atanhQ logAtanhPoly
  push_cast
  rfl

theorem atanh_lower {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    logAtanhPoly 20 r ≤ Real.log ((1 + r) / (1 - r)) := by
  have h := (log_atanh20_error hr hr1).1
  have hp : (1 + r : ℝ) ≠ 0 := by linarith
  have hm : (1 - r : ℝ) ≠ 0 := by linarith
  rw [Real.log_div hp hm]
  unfold logAtanhError at h
  linarith

/-- A true logarithm lower bound from the20-term positive atanh polynomial. -/
theorem lowerQ_sound {n two k : ℕ} (hpow : two = 2 ^ k)
    (hlow : two ≤ n) (hhigh : n < 2 * two) : (lowerQ n two k : ℝ) ≤ Real.log n := by
  have htwo : 0 < two := by rw [hpow]; positivity
  have hn : 0 < n := htwo.trans_le hlow
  have hden : 0 < n + two := by omega
  have hm0 : (0 : ℝ) ≤ (n - two : ℕ) / (n + two : ℕ) := by positivity
  have hm1 : ((n - two : ℕ) : ℝ) / (n + two : ℕ) < 1 := by
    apply (div_lt_one (by exact_mod_cast hden : (0 : ℝ) < (n + two : ℕ))).mpr
    exact_mod_cast (show n - two < n + two by omega)
  have hm := atanh_lower hm0 hm1
  have htwo0 : (0 : ℝ) < two := by exact_mod_cast htwo
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hid : (1 + (n - two : ℕ) / (n + two : ℕ) : ℝ) /
      (1 - (n - two : ℕ) / (n + two : ℕ)) = (n : ℝ) / two := by
    push_cast [Nat.cast_sub hlow]
    field_simp [htwo0.ne']
    <;> ring
  rw [hid] at hm
  have h2 := atanh_lower (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1)
  norm_num at h2
  have hlogtwo : Real.log (two : ℝ) = (k : ℝ) * Real.log 2 := by
    have hp : (two : ℝ) = (2 : ℝ) ^ k := by exact_mod_cast hpow
    rw [hp, Real.log_pow]
  have hlogn : Real.log (n : ℝ) = (k : ℝ) * Real.log 2 + Real.log ((n : ℝ) / two) := by
    rw [Real.log_div hn0.ne' htwo0.ne', hlogtwo]
    ring
  calc
    (lowerQ n two k : ℝ) = (k : ℝ) * logAtanhPoly 20 (1 / 3) +
        logAtanhPoly 20 ((n - two : ℕ) / (n + two : ℕ)) := by
      unfold lowerQ
      push_cast
      rw [atanhQ_cast, atanhQ_cast]
      norm_num
    _ ≤ (k : ℝ) * Real.log 2 + Real.log ((n : ℝ) / two) :=
      add_le_add (mul_le_mul_of_nonneg_left h2 (by positivity)) hm
    _ = Real.log n := hlogn.symm

/-- This finite exact check evaluates the actual integer algorithm, not a list
of unproved native outputs. The C refinement is a separate, genuine source proof. -/
theorem lowerCheck_true : lowerCheck = true := by decide +kernel

theorem model_lower_check {n : ℕ} (hn : 2 ≤ n) (hN : n ≤ 128) :
    (model n : ℚ) / 2 ^ 40 - 1 / 2 ^ 30 ≤ lowerQ n (two n) (exponent n) := by
  have h := (List.all_eq_true.mp lowerCheck_true) n (List.mem_range.mpr (by omega))
  have hn' : ¬n < 2 := by omega
  simpa only [hn', ↓reduceIte, decide_eq_true_eq] using h

/-- The new lower enclosure is proved, with explicit finite input domain. -/
theorem model_log_lower {n : ℕ} (hn : 2 ≤ n) (hN : n ≤ 128) :
    (model n : ℝ) / 2 ^ 40 - 1 / 2 ^ 30 ≤ Real.log n := by
  have hc := model_lower_check hn hN
  have hreal0 : (((model n : ℚ) / 2 ^ 40 - 1 / 2 ^ 30 : ℚ) : ℝ) ≤
      (lowerQ n (two n) (exponent n) : ℝ) := by
    exact Rat.cast_le.mpr hc
  have hreal : (model n : ℝ) / 2 ^ 40 - 1 / 2 ^ 30 ≤
      (lowerQ n (two n) (exponent n) : ℝ) := by
    norm_num at hreal0 ⊢
    exact hreal0
  have hnrm := normalization hn
  exact hreal.trans (lowerQ_sound rfl hnrm.1 hnrm.2)

#print axioms model_log_lower
end CLogMathLower
