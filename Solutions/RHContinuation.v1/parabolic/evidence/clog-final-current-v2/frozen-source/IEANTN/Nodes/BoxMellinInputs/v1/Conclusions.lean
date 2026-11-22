/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHSmoothing
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! Exact analytic identities supporting the box absolute Mellin moments.
The numerical log program and the desired moment/PNT bounds are not assumptions
here. These three remaining analytic claims are written continuation mathematics,
not yet complete formal proofs. Their detailed derivation is in
Solutions/RHContinuation.v1/parabolic/BOX_MELLIN_EXACT.md.
-/
namespace BoxMellinInputs.v1
open Real MeasureTheory Set
open scoped Topology

noncomputable def integrand (j : ℕ) (y : ℝ) : ℝ :=
  (|IEANTN.RHSmoothing.fourier IEANTN.RHSmoothing.box y| -
    if y ≤ 1 then 1 else 0) * (Real.log y) ^ j / y
noncomputable def stieltjesSeq (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 2 n, Real.log k / k) - (Real.log n) ^ 2 / 2
noncomputable def gamma1 : ℝ := Filter.limUnder Filter.atTop stieltjesSeq
noncomputable def qTerm (n : ℕ) : ℝ :=
  if n < 2 then 0 else Real.log n / ((n : ℝ) * (4 * n ^ 2 - 1))
noncomputable def q : ℝ := ∑' n : ℕ, qTerm n
noncomputable def a : ℝ := 1 - Real.eulerMascheroniConstant - Real.log 2

/-- The constant term of the actual regularized absolute box Mellin transform.
The written proof uses the positive Fourier series of abs(sin), Tonelli, the
Gamma integral, and an exact harmonic partial-fraction sum. -/
def first_moment : Prop :=
  IntegrableOn (integrand 0) (Ioi 0) ∧
  IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 0 = Real.log 2

/-- Exact linear Mellin coefficient, with the actual convergent logarithmic
series and the Stieltjes limit. The series summability and the finite numerical
bound are proved in the separate solution, rather than added as assumptions. -/
def second_moment_identity : Prop :=
  IntegrableOn (integrand 1) (Ioi 0) ∧
  IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 1 =
    -gamma1 - q + a * Real.log 2 - a ^ 2 / 2 + 1 / 2 + Real.pi ^ 2 / 24

/-- Actual Stieltjes-sequence convergence and its finite convex-trapezoid lower
bound at128. The source uses f(t)=log(t)/t, whose second derivative is positive
for t≥128. No desired moment or prime-number bound occurs in this premise. -/
def stieltjes_trapezoid : Prop :=
  Filter.Tendsto stieltjesSeq Filter.atTop (𝓝 gamma1) ∧
  stieltjesSeq 128 - Real.log 128 / 256 ≤ gamma1
end BoxMellinInputs.v1
