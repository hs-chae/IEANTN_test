/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitMellinIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

/-- The exact common weight used for both exterior prime wings. -/
def exteriorPrimeWeight (d L R : ℝ) : ℝ := (L+R*d)/exp ((L-R*d)/2)

theorem prime_log_weight_le_support (d L R : ℝ) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hpositive : R*d < L) (p : ℕ) (hPrime : Nat.Prime p)
    (hlo : exp (L-R*d) ≤ (p:ℝ)) (hhi : (p:ℝ) ≤ exp (L+R*d)) :
    log (p:ℝ)/sqrt (p:ℝ) ≤ exteriorPrimeWeight d L R := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast hPrime.pos
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hPrime.one_le
  have hlog : 0 ≤ log (p:ℝ) := log_nonneg hp1
  have hupper : log (p:ℝ) ≤ L+R*d := by
    have hh := log_le_log hp hhi
    rwa [log_exp] at hh
  have hlower : exp ((L-R*d)/2) ≤ sqrt (p:ℝ) := by
    have hh := sqrt_le_sqrt hlo
    rwa [←exp_half] at hh
  exact (div_le_div_of_nonneg_left hlog (exp_pos _) hlower).trans
    (div_le_div_of_nonneg_right hupper (exp_pos _).le)

/-- The interior prime weight decreases on the entire analytic domain,
including both real endpoints of each half-open interval. -/
theorem prime_log_weight_le_inside (t : ℝ) (ht : 2 ≤ t) (p : ℕ)
    (hp : exp t ≤ (p:ℝ)) :
    log (p:ℝ)/sqrt (p:ℝ) ≤ t*exp (-t/2) := by
  have hx : exp 2 ≤ exp t := exp_le_exp.mpr ht
  have h := log_div_sqrt_antitoneOn hx (hx.trans hp) hp
  change log (p:ℝ)/sqrt (p:ℝ) ≤ log (exp t)/sqrt (exp t) at h
  rw [log_exp,←exp_half] at h
  have heq : t/exp (t/2) = t*exp (-t/2) := by rw [show -t/2 = -(t/2) by ring,exp_neg]; ring
  rwa [heq] at h

/-- Actual von-Mangoldt prime terms, with no signed-window shortcut: W is
bounded above through its proved absolute bound before the weight is used. -/
theorem interior_prime_term_le (nodes : List ℚ) (m : ℕ) (d L M t : ℝ)
    (hM : 0 ≤ M) (hW : ∀ v : ℝ, |affineSpectrum nodes m v| ≤ M)
    (ht : 2 ≤ t) (p : CMSPrimeIndex) (hPrime : Nat.Prime (p:ℕ))
    (hlo : exp t ≤ (p:ℕ)) :
    weightedMangoldtFamily nodes m d L p ≤ M*t*exp (-t/2) := by
  have hp1 : (1:ℝ) ≤ (p:ℕ) := by exact_mod_cast hPrime.one_le
  have hweight : 0 ≤ log (p:ℕ)/sqrt (p:ℕ) := div_nonneg (log_nonneg hp1) (sqrt_nonneg _)
  unfold weightedMangoldtFamily mellinArithmeticWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime hPrime]
  calc
    _ = affineSpectrum nodes m ((log (p:ℕ)-L)/d)*(log (p:ℕ)/sqrt (p:ℕ)) := by ring
    _ ≤ M*(log (p:ℕ)/sqrt (p:ℕ)) :=
      mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hW _)) hweight
    _ ≤ M*(t*exp (-t/2)) := mul_le_mul_of_nonneg_left (prime_log_weight_le_inside t ht (p:ℕ) hlo) hM
    _ = _ := by ring

#print axioms prime_log_weight_le_support
#print axioms interior_prime_term_le
end RH080Next.Explicit
