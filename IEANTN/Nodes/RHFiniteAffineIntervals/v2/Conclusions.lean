/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Real
namespace RHFiniteAffineIntervals.v2

/-- Every real4≤x≤exp174 has a prime strictly inside the0.8sqrt(x)log(x)
interval. RH, the named analytic source inputs, original Fap norm provider and
historical finite gap computation remain explicit challenge imports. -/
def interval_08_full : Prop :=
  ∀ x : ℝ, 4≤x → x≤exp 174 → ∃p : ℕ, Nat.Prime p ∧ x<(p:ℝ) ∧
    (p:ℝ)<x+(4/5:ℝ)*sqrt x*log x

/-- Original0.74 coefficient on the complete real11≤x≤exp63 range, preserving
both strict prime endpoints and every analytic/finite-computation input. -/
def interval_074_full : Prop :=
  ∀ x : ℝ, 11≤x → x≤exp 63 → ∃p : ℕ, Nat.Prime p ∧ x<(p:ℝ) ∧
    (p:ℝ)<x+(37/50:ℝ)*sqrt x*log x

/-- Original0.75 coefficient on the complete real11≤x≤exp70 range. This is a
finite-range theorem, not an asymptotic assertion or a global optimum. -/
def interval_075_full : Prop :=
  ∀ x : ℝ, 11≤x → x≤exp 70 → ∃p : ℕ, Nat.Prime p ∧ x<(p:ℝ) ∧
    (p:ℝ)<x+(3/4:ℝ)*sqrt x*log x

/-- Elementary exact small branch: genuine primes5,7,11 give the strict0.777
interval on every real4≤x<11. This conclusion needs no RH, analytic source,
numerical-provider or historical-computation assumption. -/
def interval_0777_small : Prop :=
  ∀ x : ℝ, 4≤x → x<11 → ∃p : ℕ, Nat.Prime p ∧ x<(p:ℝ) ∧
    (p:ℝ)<x+(777/1000:ℝ)*sqrt x*log x

end RHFiniteAffineIntervals.v2
