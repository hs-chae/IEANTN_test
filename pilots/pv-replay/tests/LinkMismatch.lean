/-
Negative control for the A→B′ data link. This file must NOT elaborate.

B′ was certified at `M = 120 + 0.0914`, A's certified deviation. A chain that feeds B′ a different
deviation, here `0.0913`, needs the link `B′.M = 120 + 0.0913`; that equality is false, so the
existing link theorem cannot be used for it and no proof of it exists.
-/
import PVReplay.Chain

open CalibrationPilot

/-- The mismatched link is refutable outright. -/
theorem link_mismatch_is_false : ((NewB.M : ℚ) : ℝ) ≠ 120 + ((913 / 10000 : ℚ) : ℝ) := by
  norm_num [NewB.M]

/-- Reusing the certified link for the mismatched deviation: rejected by the kernel. -/
theorem link_mismatch : ((NewB.M : ℚ) : ℝ) = 120 + ((913 / 10000 : ℚ) : ℝ) :=
  PVPilot.Updated.link
