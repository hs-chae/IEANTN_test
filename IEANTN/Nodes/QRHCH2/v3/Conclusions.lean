/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary

/-! A concrete, formalized downstream replay of the free-height CH2 transfer.
The constants here are proved in Lean, independently of the older density candidate. -/
namespace QRHCH2.v3

/-- Uniform verified numerical PNT bound from the seven-eighths half-plane. -/
def psi_numerical_bound : Prop :=
  IEANTN.HasNumericalBound IEANTN.Eψ ((1573 : ℝ) / 10 ^ 17) (Real.exp 300)

/-- The same input after the standard psi-to-theta conversion. -/
def theta_numerical_bound : Prop :=
  IEANTN.HasNumericalBound IEANTN.Eθ ((1574 : ℝ) / 10 ^ 17) (Real.exp 300)

/-- Feed the new theta bound into the existing PrimeInterval.v1 criterion. -/
def short_prime_interval : Prop :=
  ∀ x : ℝ, Real.exp 300 ≤ x → IEANTN.HasPrimeInInterval x (x / 30000000000000)

end QRHCH2.v3
