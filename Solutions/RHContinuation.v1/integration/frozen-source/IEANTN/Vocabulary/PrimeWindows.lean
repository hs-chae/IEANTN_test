/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHSmoothing
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
namespace IEANTN.PrimeWindows
open Real MeasureTheory Set Finset
noncomputable def primeCounting (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊
noncomputable def primesBetween (a b : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊b⌋₊).filter fun p => a < (p : ℝ) ∧ (p : ℝ) < b
noncomputable def kernel (n : ℕ) (u : ℝ) : ℝ := max 0 (1 - u ^ (2 * n))
noncomputable def mass (n : ℕ) : ℝ := 4 * (n : ℝ) / (2 * (n : ℝ) + 1)
noncomputable def D (C L : ℝ) : ℝ := C / 2 * L - 1
noncomputable def δ (C L : ℝ) : ℝ := D C L * Real.exp (-L / 2)
noncomputable def a (C L : ℝ) : ℝ := Real.exp (L - δ C L)
noncomputable def b (C L : ℝ) : ℝ := Real.exp (L + δ C L)
noncomputable def population (n : ℕ) (C L : ℝ) : ℝ :=
  ∑ p ∈ primesBetween (a C L) (b C L),
    kernel n ((Real.log p - L) / δ C L) * (Real.log p / Real.sqrt p)
noncomputable def mangoldtPopulation (n : ℕ) (C L : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (⌊b C L⌋₊ + 1)).filter
      (fun k : ℕ => a C L < (k : ℝ) ∧ (k : ℝ) < b C L),
    kernel n ((Real.log (k : ℝ) - L) / δ C L) *
      ((ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt (k : ℝ))
noncomputable def transform (n : ℕ) (y : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, kernel n u * Real.cos (y * u)
noncomputable def zeroPacket (n : ℕ) (C L : ℝ) (ρ : IEANTN.RHSmoothing.Zero) : ℂ :=
  Complex.exp (Complex.I * ((ρ : ℂ).im * L : ℝ)) *
    (δ C L * transform n (δ C L * (ρ : ℂ).im) : ℝ) *
    (IEANTN.zetaOrder ρ : ℂ)
noncomputable def zeroTerm (n : ℕ) (C L : ℝ) : ℂ :=
  ∑' ρ : IEANTN.RHSmoothing.Zero, zeroPacket n C L ρ
noncomputable def mainTerm (n : ℕ) (C L : ℝ) : ℝ :=
  D C L * ∫ u in (-1 : ℝ)..1, kernel n u * Real.cosh (δ C L * u / 2)
noncomputable def trivialCost (n : ℕ) (C L : ℝ) : ℝ :=
  ∫ t in a C L..b C L, kernel n ((Real.log t - L) / δ C L) /
    (Real.sqrt t * t * (t ^ 2 - 1))
noncomputable def countCoefficient (n : ℕ) (A C : ℝ) : ℝ := mass n * C / 2 - A / 2

def ExplicitFormula (n : ℕ) (C : ℝ) : Prop := RiemannHypothesis →
  ∀ L : ℝ, 24 ≤ L → Summable (zeroPacket n C L) ∧
    mangoldtPopulation n C L = mainTerm n C L - (zeroTerm n C L).re - trivialCost n C L

def ZeroEstimate (n : ℕ) (C A B R : ℝ) : Prop := RiemannHypothesis →
  ∀ L : ℝ, 24 ≤ L → ‖zeroTerm n C L‖ ≤
    A * (L / 2 - Real.log (2 * Real.pi * D C L)) + B + R

def PrimePowerCost (n : ℕ) (C P : ℝ) : Prop :=
  ∀ L : ℝ, 24 ≤ L → mangoldtPopulation n C L - population n C L ≤ P

def TrivialCost (n : ℕ) (C T : ℝ) : Prop :=
  ∀ L : ℝ, 24 ≤ L → trivialCost n C L ≤ T

/-- Exact scalar geometry and logarithmic margin; contains no prime-count goal. -/
def ScalarGeometry (n : ℕ) (C A B R P T η : ℝ) : Prop :=
  ∀ L : ℝ, 24 ≤ L → 0 < a C L ∧ 2 ≤ Real.log (a C L) ∧
    a C L ≤ b C L ∧ L - δ C L = Real.log (a C L) ∧ 0 ≤ δ C L ∧
    0 ≤ D C L ∧ 0 ≤ countCoefficient n A C ∧ 0 < η ∧
    η < A * Real.log (2 * Real.pi * D C L) - mass n - B - R - P - T

def ForwardCoverage (C : ℝ) : Prop := ∀ u : ℝ, Real.exp 24 ≤ u →
  ∃ L : ℝ, 24 ≤ L ∧ a C L = u ∧
    b C L ≤ u + C * Real.sqrt u * Real.log u


end IEANTN.PrimeWindows
