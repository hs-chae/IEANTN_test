/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OriginalBoundaryScalars
namespace WinnerOriginalScalars
open Real
set_option maxHeartbeats 0

/-- The source's X^q and our evaluated exp(q logX) agree on every proof-bearing use. -/
theorem bsix_source_form {X q gamma : ℝ} (hX : 0<X) :
    sourceBSix X q gamma=(1+q)*log X/(q*X^q)*
      (1+1/(q*log X)+gamma/log X+7*q/(12*(1+q)*X*log X)) := by
  unfold sourceBSix
  rw [rpow_def_of_pos hX]
  ring

/-- Exact KLN(4.63) written with the original power notation. -/
theorem ceight_source_form (gamma : ℝ) :
    sourceCEight gamma=sourceBTen gamma*(log height)^2/height^(2*boundaryMu-2)*
      (4*boundaryMu*sourceBEleven (2*boundaryMu)/(2*boundaryMu-1)+
       2*Real.pi*sourceM0*(2*boundaryMu-1)*sourceBEleven (2*boundaryMu-1)/(boundaryMu-1)) := by
  unfold sourceCEight sourceCEightBase
  rw [rpow_def_of_pos (by norm_num [height])]
  ring

#print axioms bsix_source_form
#print axioms ceight_source_form
end WinnerOriginalScalars
