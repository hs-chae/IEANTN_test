/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import G40Sources

set_option autoImplicit false
noncomputable section
namespace RH080.Gaussian40

/-- The fixed Laguerre-degree40 / physical-degree80 candidate. Definitions are
independent of every numerical certificate or proposed bound. -/
def physicalF (x : ℝ) : ℝ :=
  coeffEval normSource (Real.sqrt Real.pi*x) * Real.exp (-((Real.sqrt Real.pi*x)^2))

/-- Candidate Fourier partner, whose actual Fourier association is proved in
the separate Primal80Fourier modules. No Fourier identity is assumed here. -/
def physicalG (x : ℝ) : ℝ :=
  coeffEval wingSource (Real.sqrt Real.pi*x) * Real.exp (-((Real.sqrt Real.pi*x)^2))

end RH080.Gaussian40
