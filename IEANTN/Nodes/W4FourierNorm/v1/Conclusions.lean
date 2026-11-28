/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.AffineFourierWindow
import IEANTN.Nodes.W4FourierNorm.v1.Tables
noncomputable section
open Real MeasureTheory IEANTN.AffineFourierWindow
namespace W4FourierNorm.v1

/-- Original support-seven whole-line norm bound, with unchanged data and
16777216-cell integer-FFT algorithm. Its solution must consume the actual
complete C main and printf result; the general BR norm identity stays explicit. -/
def l1_bound : Prop :=
  (∫ u : ℝ,|inverseCosine (affineSpectrum Tables.affineNodes 360) u|)≤
    (7813568381304104:ℝ)/10000000000000000
end W4FourierNorm.v1
