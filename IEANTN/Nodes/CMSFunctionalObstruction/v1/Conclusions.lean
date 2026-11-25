/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.CMSDual
import IEANTN.Nodes.CMSDualCertificate.v1.Conclusions

set_option autoImplicit false
noncomputable section
namespace CMSFunctionalObstruction.v1

/-- New study conclusion; source/verification status remains in metadata.
The ratio scope is the actual L1-Fourier fragment, not all prime-gap methods. -/
def ratio_floor : Prop := IEANTN.CMSDual.L1RatioFloor (36/11 : ℝ) (100/123 : ℝ)

/-- New study conclusion; source/verification status remains in metadata.
The ratio scope is the actual L1-Fourier fragment, not all prime-gap methods. -/
def excludes_four_fifths : Prop := IEANTN.CMSDual.L1RatioStrictlyAbove (36/11 : ℝ) (4/5 : ℝ)

end CMSFunctionalObstruction.v1
