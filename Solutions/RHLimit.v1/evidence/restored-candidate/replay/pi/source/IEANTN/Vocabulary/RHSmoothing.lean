/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Zeta
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Actual smoothing observables shared by provider and downstream consumer nodes.
Only definitions. Zero packets include actual zeta multiplicity. Analytic input
nodes require summability; no totalized sum is treated as proof evidence. -/
namespace IEANTN.RHSmoothing
open Real MeasureTheory Set
noncomputable def parabola (u : ℝ) : ℝ := (3 / 4 : ℝ) * (1 - u ^ 2)
noncomputable def box (_u : ℝ) : ℝ := 1 / 2
noncomputable def v (L : ℝ) : ℝ := L / 2 - Real.log L
noncomputable def delta (L : ℝ) : ℝ := L / (2 * Real.pi * Real.sqrt (Real.exp L))
noncomputable def average (k : ℝ → ℝ) (s L : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, k u * Chebyshev.psi
    (Real.exp L * Real.exp ((s + u) * delta L))
noncomputable def mainAverage (k : ℝ → ℝ) (s L : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, k u *
    (Real.exp L * Real.exp ((s + u) * delta L))
noncomputable def trivial (t : ℝ) : ℝ := -(Real.log (1 - t ^ (-2 : ℤ))) / 2
noncomputable def trivialAverage (k : ℝ → ℝ) (s L : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, k u * trivial
    (Real.exp L * Real.exp ((s + u) * delta L))
noncomputable def fourier (k : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, k u * Real.cos (y * u)
noncomputable def J (k : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ),
    (|fourier k y| - if y ≤ 1 then 1 else 0) * (Real.log y) ^ j / y
abbrev Zero := IEANTN.zetaZeroesIn (Set.Ioo 0 1) Set.univ
noncomputable def zeroPacket (k : ℝ → ℝ) (s L : ℝ) (ρ : Zero) : ℂ :=
  (Real.exp L : ℂ) ^ (ρ : ℂ) / (ρ : ℂ) *
    (∫ u in (-1 : ℝ)..1, (k u : ℂ) *
      Complex.exp ((ρ : ℂ) * (((s + u) * delta L : ℝ) : ℂ))) *
    (IEANTN.zetaOrder ρ : ℂ)
noncomputable def zeroAverage (k : ℝ → ℝ) (s L : ℝ) : ℂ :=
  ∑' ρ : Zero, zeroPacket k s L ρ
noncomputable def envelope (j0 j1 L : ℝ) : ℝ :=
  (v L ^ 2 + 2 * j0 * v L + 2 * j1 + L) / (2 * Real.pi) + 14 / 100


noncomputable def fastBound (L : ℝ) : ℝ := envelope (Real.log 2) (567 / 800) L
noncomputable def chBound (L : ℝ) : ℝ :=
  let u := L / 2 - Real.log L + Real.log (10 / Real.pi)
  (158 / 1000) * L + (u ^ 2 - u / 3) / (2 * Real.pi) + 181 / 1000
end IEANTN.RHSmoothing
