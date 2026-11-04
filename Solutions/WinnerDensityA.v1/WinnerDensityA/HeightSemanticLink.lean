/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.HeightProgram
import WinnerDensityA.HeightMoment
namespace WinnerDensityA
open Real
set_option maxHeartbeats 0
/-- The executed four-height expression denotes the actual proved moment
budget. The lower tails are subtracted with their proved direction. -/
theorem height_envelope_link (s τ : ℝ) :
    HeightProgram.mathEnvelope s τ=WinnerHeightMoment.envelope s τ := by
  have h1:=HeightExpression.lower_real s 1 (by norm_num)
  have h2:=HeightExpression.lower_real s 2 (by norm_num)
  have h4:=HeightExpression.lower_real s 4 (by norm_num)
  unfold HeightProgram.mathEnvelope HeightProgram.correction
  rw [h1,h2,h4]
  unfold WinnerDensityA.envelope WinnerDensityA.moment WinnerHeightMoment.envelope
    WinnerHeightMoment.moment WinnerHeightMoment.coeff WinnerHeightMoment.p WinnerHeightMoment.q
    ModelProgram.modelC
  rw [←HeightExpression.initial_upper]
  norm_num [WinnerHeightProfiles.row,WinnerHeightProfiles.anchor,
    WinnerOriginalScalars.height,H] <;> push_cast <;> ring
#print axioms height_envelope_link
end WinnerDensityA
