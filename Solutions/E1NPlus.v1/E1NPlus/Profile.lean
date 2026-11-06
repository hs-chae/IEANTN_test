/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.Common
import PVEvolutionA.SlopedMoment
namespace E1NPlus.Profile
open Real Set
set_option maxHeartbeats 0
/-- Only the frozen row3 profile is consumed; no new calibration or program run. -/
theorem source_count_closed
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {s T : ℝ} (hs : (3 / 4 : ℝ) ≤ s) (hs' : s ≤ 7 / 8) (hT : E1NPlus.profileHeight ≤ T) :
    IEANTN.zetaZeroesSum (Ioo s 1) (Ioc 0 T) (fun _ ↦ (1 : ℝ))≤E1NPlus.densityMajorant s T := by
  have ha:WinnerHeightProfiles.anchor (3:Fin 4)=E1NPlus.profileHeight := by
    norm_num [WinnerHeightProfiles.anchor,WinnerHeightProfiles.anchor,
      WinnerHeightProfiles.row,WinnerOriginalScalars.height,E1NPlus.profileHeight]
  have hc:=PVEvolutionA.SlopedMoment.profile_count_closed h hRH (3:Fin 4) hs hs' (ha.trans_le hT)
  norm_num [WinnerDensityA.poly,PVEvolutionA.SlopedMoment.coeff,PVEvolutionA.SlopedMoment.slope,
    WinnerHeightProfiles.row,E1NPlus.densityMajorant,E1NPlus.coeff,E1NPlus.K,E1NPlus.B,E1NPlus.p,E1NPlus.q] at hc ⊢
  exact hc
#print axioms source_count_closed
end E1NPlus.Profile
