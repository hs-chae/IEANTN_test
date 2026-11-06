/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.MomentRay
import DirectIntervalA.EvolvedCertificate

namespace DirectIntervalA
open Real Set

theorem evolved_high_ray {L : ℝ} (hL : (330 : ℝ)≤L) : high L ≤ (355513/1000000 : ℝ) := by
  exact (high_antitone (show (330 : ℝ)∈Ici 330 by simp) hL hL).trans Evolved.high330_le

end DirectIntervalA
#print axioms DirectIntervalA.evolved_high_ray
