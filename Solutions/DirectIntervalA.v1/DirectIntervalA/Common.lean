/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityTailMoments
import Mathlib.Tactic

open Real Set MeasureTheory

namespace DirectIntervalA

noncomputable abbrev k : ℝ := 201 / 100
abbrev start : ℝ := 330

noncomputable def delta (L : ℝ) : ℝ := exp (-L / 5)
noncomputable def U (L : ℝ) : ℝ := k * exp (L / 5)
noncomputable def truncHeight (L : ℝ) : ℝ := 120 * L * exp (L / 5)
noncomputable def V (L : ℝ) : ℝ := 2 * truncHeight L

noncomputable def moment (s H : ℝ) : ℝ :=
  (9795 / 1000 : ℝ) * CH2QRH.densityMomentMain s H +
    (4465 / 1000 : ℝ) * ((log H ^ (2 : ℕ) + 2 * log H + 2) / H)

noncomputable def high (L : ℝ) : ℝ :=
  2 * k * L * exp (L / 5) *
    ∫ s in (3 / 4 : ℝ)..(7 / 8 : ℝ), exp (-(1 - s) * L) * moment s (U L)

noncomputable def low (L : ℝ) : ℝ :=
  2 * k * exp (-L / 20) * (log (V L) + log (V L) ^ (2 : ℕ) / 2)

theorem moment_bound {s H T : ℝ} (hH : 1 < H) (hHT : H ≤ T)
    (hs : (3 / 4 : ℝ) ≤ s) (hs' : s ≤ 7 / 8) :
    CH2QRH.fksDensityMajorant s T / T +
      (∫ t in H..T, CH2QRH.fksDensityMajorant s t / t ^ 2) ≤ moment s H := by
  convert CH2QRH.fks_density_reciprocal_moment_bound hH hHT hs hs' using 1 <;>
    norm_num [moment]

end DirectIntervalA

#print axioms DirectIntervalA.moment_bound
