/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.MomentRay
import DirectIntervalA.NumericalCertificate

namespace DirectIntervalA
open Real Set

/-- The actual composed numerical program controls the whole real logarithmic ray. -/
theorem high_ray {L : ℝ} (hL : (330 : ℝ)≤L) : high L ≤ (179257/500000 : ℝ) := by
  exact (high_antitone (show (330 : ℝ)∈Ici 330 by simp) hL hL).trans
    Numerical.high330_le

theorem high_ray_036 {L : ℝ} (hL : (330 : ℝ)≤L) : high L ≤ (36/100 : ℝ) := by
  exact (high_ray hL).trans (by norm_num)

end DirectIntervalA
#print axioms DirectIntervalA.high_ray
