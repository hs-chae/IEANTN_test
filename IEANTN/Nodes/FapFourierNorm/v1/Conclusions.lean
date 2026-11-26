/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.AffineFourierWindow
import IEANTN.Nodes.FapFourierNorm.v1.Tables

noncomputable section
open Real MeasureTheory IEANTN.AffineFourierWindow
namespace FapFourierNorm.v1

/-- Original Fap whole-line norm bound, proved by the complete131072-point
integer FFT, true DFT error and actual periodic quadrature. Its only analytic
norm identity input is BRFourierInput.v1.norm_identity. Kernel-only numerical
verification; source-first PV of the full C FFT is not claimed. -/
def l1_bound : Prop :=
  (∫ u : ℝ, |inverseCosine (affineSpectrum Tables.affineNodes 80) u|) ≤
    (7817960157900848:ℝ)/10000000000000000

end FapFourierNorm.v1
