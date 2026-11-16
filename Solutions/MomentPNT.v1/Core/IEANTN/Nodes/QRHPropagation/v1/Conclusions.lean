/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PowerError
import IEANTN.Vocabulary.PrimeGaps
import IEANTN.Nodes.FKS2.v2.Conclusions

/-! Derived interfaces; genuine QRH enters through the explicitly recorded refined psi bound. -/
namespace QRHPropagation.v1
open Real IEANTN

/-- Keep the complete pointwise power saving in theta, not only a uniform error floor. -/
def theta_power_bound : Prop := HasPowerLogBound Eθ (1 / 283) 2 (7 / 8) (exp 300)

/-- The offset logarithmic integral is used, exactly as in the existing Epi vocabulary. -/
def pi_power_bound : Prop := HasPowerLogBound Eπ (1 / 280) 2 (7 / 8) (exp 400)

/-- A genuinely shrinking relative interval width; open left and closed right. -/
def short_prime_intervals : Prop :=
  ∀ x ≥ exp 320, HasPrimeInInterval x ((4 / 283 : ℝ) * log x ^ 2 * x ^ ((7 : ℝ) / 8))

/-- Replay existing FKS2 Theorem3 with its exact correction, not a guessed rounded constant. -/
def fks2_classical_replay : Prop :=
  HasClassicalBound Eπ
    ((1 + FKS2.v2.muAsymp (1 / 283) 2 2 1 (exp 300) (exp 400)) * (1 / 283))
    2 2 1 (exp 400)

/-- The density frontier yields a log-free theta bound with an elementary allowance. -/
def theta_density_bound : Prop := HasPowerLogBound Eθ (1 / 50) 0 (7 / 8) (exp 300)

/-- Partial summation retains the log-free power saving for pi. -/
def pi_density_bound : Prop := HasPowerLogBound Eπ (21 / 1000) 0 (7 / 8) (exp 600)

/-- Every real x>=e^300 has a prime in (x,x+0.08*x^(7/8)]. -/
def density_prime_intervals : Prop :=
  ∀ x ≥ exp 300, HasPrimeInInterval x ((2 / 25 : ℝ) * x ^ ((7 : ℝ) / 8))

end QRHPropagation.v1
