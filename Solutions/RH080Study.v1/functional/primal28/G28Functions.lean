/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import G28Sources
set_option autoImplicit false
noncomputable section
namespace RH080.Gaussian28
open RH080.Gaussian40
/-- Frozen timely trial candidate: Laguerre degree28, physical degree56.
No numerical bound or Fourier identity is assumed by these definitions. -/
def physicalF (x : ℝ) : ℝ :=
  coeffEval normSource (Real.sqrt Real.pi*x) * Real.exp (-((Real.sqrt Real.pi*x)^2))
def physicalG (x : ℝ) : ℝ :=
  coeffEval wingSource (Real.sqrt Real.pi*x) * Real.exp (-((Real.sqrt Real.pi*x)^2))
end RH080.Gaussian28
