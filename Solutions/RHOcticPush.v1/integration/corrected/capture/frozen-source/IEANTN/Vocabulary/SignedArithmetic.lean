/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Meromorphic.Order

/-! Actual signed prime sums, Euler products, and Mobius observables.
Definitions only. An unordered zero sum is useful only with an explicit
summability guard supplied by a node claim; no simple-zero convention is used.
All finite sums use ordinary inclusive natural-floor endpoints. -/
namespace IEANTN.SignedArithmetic
open Finset ArithmeticFunction
noncomputable def primes (x : ℝ) : Finset ℕ := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
noncomputable def A (x : ℝ) : ℝ := ∑ p ∈ primes x, Real.log p / p
noncomputable def CA (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / n
noncomputable def q (n : ℕ) : ℝ :=
  if n.Prime then Real.log n / ((n : ℝ) * (n - 1 : ℝ)) else 0
noncomputable def correctionConstant : ℝ := ∑' n : ℕ, q n
noncomputable def E : ℝ := - Real.eulerMascheroniConstant - correctionConstant

def PaperZero := {s : ℂ // 0 < s.re ∧ s.re < 1 ∧ s.im ≠ 0 ∧ riemannZeta s = 0}
/-- Actual order of vanishing; counted with multiplicity, rather than enumerating distinct
zeros as if all were simple. This is Mathlib's meromorphic order, converted to Nat. -/
noncomputable def zeroMultiplicity (s : PaperZero) : ℕ :=
  ((meromorphicOrderAt riemannZeta s.val).untopD 0).toNat
noncomputable def reciprocalWeight (s : PaperZero) : ℝ :=
  (zeroMultiplicity s : ℝ) / s.val.im^2
noncomputable def reciprocalMass : ℝ := ∑' s : PaperZero, reciprocalWeight s
/-- BFKNW (29), specialized to m=1, on the actual zero domain and multiplicities. -/
noncomputable def J1 (x : ℝ) : ℝ :=
  ∑' s : PaperZero, (zeroMultiplicity s : ℝ) * x^(s.val.re-1) / s.val.im^2

noncomputable def beta : ℝ :=
  2+Real.eulerMascheroniConstant-Real.log Real.pi-2*Real.log 2

noncomputable def product (x : ℝ) : ℝ :=
  ∏ p ∈ primes x, (1-1/(p:ℝ))⁻¹

/-- The actual source's f, Eq(1.9). -/
noncomputable def f (x : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Chebyshev.theta x) *
    ∏ p ∈ primes x, (1-1/(p:ℝ))

/-- All nontrivial zeros, with the source's multiplicity convention. -/
def ProductZero := {s : ℂ // 0<s.re ∧ s.re<1 ∧ riemannZeta s=0}
noncomputable def multiplicity (s : ProductZero) : ℕ :=
  ((meromorphicOrderAt riemannZeta s.val).untopD 0).toNat
/-- Nicolas Eq(1.18), ordinary positive real x and conjugate-paired real part. -/
noncomputable def spectralTerm (x : ℝ) (s : ProductZero) : ℂ :=
  (multiplicity s:ℂ) * (x:ℂ)^(Complex.I*(s.val.im:ℂ)) / (s.val*(1-s.val))
noncomputable def W (x : ℝ) : ℝ := (∑' s : ProductZero,spectralTerm x s).re


noncomputable def profile (x : ℝ) : ℝ :=
  2-beta-(2+beta)/Real.log x-4*beta/(Real.log x)^2-
    Real.sqrt x*Real.log x/(2*(x-1))


noncomputable def mobiusM (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ)
noncomputable def mobiusm (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / n
end IEANTN.SignedArithmetic
