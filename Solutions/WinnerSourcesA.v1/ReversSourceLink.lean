/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ReversSharpScalars
import SourceDensityPoly
namespace WinnerOriginalScalars.Revers
open Real WinnerDensitySource
set_option maxHeartbeats 0

 theorem phi_link : interpolationPhi (3119/10000) (643/500) (17/2)=sourceSharpPhi := by rfl

 theorem coefficient_link : densityCoefficient (7/8) (851/2500) (3119/10000)
    (601/5000) (643/500) (17/2) sourceSmoothingR = sourceSharpKappa := by
  unfold densityCoefficient interpolationCoefficient
  rw [phi_link]
  norm_num only [show (2:ℝ)*(1-7/8)=1/4 by norm_num,
    show (2:ℝ)*(7/8)-1=3/4 by norm_num]
  norm_num [sourceSharpKappa]
  ring

 theorem actual_coefficient_upper : densityCoefficient (7/8) (851/2500) (3119/10000)
    (601/5000) (643/500) (17/2) sourceSmoothingR ≤ 15/2 := by
  rw [coefficient_link]
  exact source_sharp_kappa_upper

 theorem actual_slope_lower : (547/100:ℝ) ≤
    2*log ((17/2)/(643/500))+4*(3119/10000)*interpolationPhi (3119/10000) (643/500) (17/2) := by
  rw [phi_link]
  exact source_sharp_slope_lower

#print axioms actual_coefficient_upper
#print axioms actual_slope_lower
end WinnerOriginalScalars.Revers
