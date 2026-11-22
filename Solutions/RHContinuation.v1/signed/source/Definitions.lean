/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set
noncomputable def primes (x : ℝ) : Finset ℕ := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
noncomputable def A (x : ℝ) : ℝ := ∑ p ∈ primes x, Real.log p / p
noncomputable def CA (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / n
noncomputable def q (n : ℕ) : ℝ :=
  if n.Prime then Real.log n / ((n : ℝ) * (n - 1 : ℝ)) else 0
noncomputable def correctionConstant : ℝ := ∑' n : ℕ, q n
noncomputable def E : ℝ := - Real.eulerMascheroniConstant - correctionConstant
noncomputable def fullTail (x : ℝ) : ℝ := correctionConstant - (CA x - A x)
noncomputable def squareFinite (y M : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊y⌋₊ ⌊M⌋₊).filter Nat.Prime, Real.log n / (n : ℝ) ^ 2
/-- Absolute convergence in BFKNW (6), after geometric summation over each prime. -/
def PublishedCorrectionSummable : Prop := Summable q
/-- BFKNW Proposition29(ii)(154), with the explicitly sourced RH zero-sum bound
J1(x)≤.0476/sqrt(x) and log(2π)<2 inserted. The source derivation is written separately. -/
def PublishedBFKNW_CA_RH : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
    |CA x - Real.log x + Real.eulerMascheroniConstant| ≤
      |Chebyshev.psi x - x| / x + 0.0476 / Real.sqrt x + 2 / x
/-- Büthe Theorem2(1.5), original ordinary endpoint convention. -/
def PublishedButhePsi : Prop := ∀ x : ℝ, 11 < x → x ≤ (10 : ℝ)^19 →
  |Chebyshev.psi x - x| ≤ 0.94 * Real.sqrt x
/-- Büthe Theorem2(1.6), finite lower bound for theta. -/
def PublishedButheThetaLower : Prop := ∀ x : ℝ, 1423 ≤ x → x ≤ (10 : ℝ)^19 →
  x - 1.95 * Real.sqrt x ≤ Chebyshev.theta x
/-- Büthe Theorem2(1.7), finite strict upper bound for theta. -/
def PublishedButheThetaUpper : Prop := ∀ x : ℝ, 1 ≤ x → x ≤ (10 : ℝ)^19 →
  Chebyshev.theta x < x - 0.05 * Real.sqrt x

theorem q_nonneg (n : ℕ) : 0 ≤ q n := by
  unfold q
  split_ifs with hp
  · have hp1 : (1 : ℝ) < n := by exact_mod_cast hp.one_lt
    exact div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  · rfl

theorem normalized_identity (x : ℝ) :
    A x - Real.log x - E =
      (CA x - Real.log x + Real.eulerMascheroniConstant) + fullTail x := by
  unfold E fullTail
  ring
end MertensPositive
