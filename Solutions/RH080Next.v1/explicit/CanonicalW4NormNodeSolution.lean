/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTW4MainNumerics
import FapSourceInterfaces
import IEANTN.Nodes.W4FourierNorm.v1.Conclusions
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section

/-- Exact equality of the canonical data-only input with the original
actual-source mathematical input. No output or new witness is substituted. -/
theorem RH080Next.CanonicalW4.original_nodes :
    W4FourierNorm.v1.Tables.affineNodes=RH080Next.WindowPV.Data.affineNodes := rfl

/-- The original norm conclusion consumes the complete actual C main/printf
provider. Generic compiler/ABI/stdio/OS/hardware contracts remain explicit. -/
theorem W4FourierNorm.v1.challenge_l1_bound
    (h : BRFourierInput.v1.norm_identity) : W4FourierNorm.v1.l1_bound := by
  change (∫u:ℝ,|RH080Next.Explicit.inverseCosine
    (RH080Next.Explicit.affineSpectrum W4FourierNorm.v1.Tables.affineNodes 360) u|)≤
      (7813568381304104:ℝ)/10000000000000000
  rw [RH080Next.CanonicalW4.original_nodes]
  exact RH080Next.FFTPV.W4Main.source_first_actual_norm h

