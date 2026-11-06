/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.ProfileFamily
import PVEvolutionA.Recovery.ManyStep
namespace PVEvolutionA.Recovery.Model
open Real Set MeasureTheory
set_option maxHeartbeats 0
noncomputable def p (sigma : ℝ) := 8*(1-sigma)/3
noncomputable def q (sigma : ℝ) := 5-2*sigma
noncomputable def step (sigma t : ℝ) :=
  ManyStep.majorant Profiles.anchor (Profiles.coeff sigma) 127 (p sigma) (q sigma) 6 t
noncomputable def moment (sigma : ℝ) :=
  ManyStep.budget Profiles.anchor (Profiles.coeff sigma) 127 (p sigma) (q sigma) 6 WinnerDensityA.H
noncomputable def envelope (sigma tau : ℝ) :=
  2*moment sigma+4*Real.pi*(WinnerDensityA.poly (Profiles.coeff sigma 0) 6 sigma (exp tau)/exp tau)
end PVEvolutionA.Recovery.Model
