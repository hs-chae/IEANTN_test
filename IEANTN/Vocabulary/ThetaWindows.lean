/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.Chebyshev
namespace IEANTN.ThetaWindows
/-- Primes in a strictly open real interval; the same membership convention as
`IEANTN.PrimeWindows.primesBetween`, isolated from smoothing vocabulary. -/
noncomputable def openPrimes (a b : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊b⌋₊).filter fun p => a < (p : ℝ) ∧ (p : ℝ) < b
/-- Schoenfeld's refined theta error function; only used on its stated domain. -/
noncomputable def schoenfeldError (x : ℝ) : ℝ :=
  Real.sqrt x * (Real.log x-2)*Real.log x/(8*Real.pi)
/-- Source-aware endpoint subtraction, with one possible prime removed at the
upper endpoint. This is an actual lower bound, not a numerical evaluation. -/
noncomputable def cubeSchoenfeldLower (n : ℝ) : ℝ :=
  (((n+1)^3-n^3-schoenfeldError (n^3)-schoenfeldError ((n+1)^3))/
  Real.log ((n+1)^3)-1)
/-- Signed finite theta envelope: the lower endpoint has theta(a)<a. -/
noncomputable def cubeButheLower (n : ℝ) : ℝ :=
  (((n+1)^3-n^3-(39/20:ℝ)*Real.sqrt ((n+1)^3))/Real.log ((n+1)^3)-1)
end IEANTN.ThetaWindows
