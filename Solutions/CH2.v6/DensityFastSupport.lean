/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityFastFinSum
open Lean Elab Tactic
elab "density_fast_finsum" depth:num : tactic => do
  match ← LeanCert.Tactic.DensityFast.finSumBoundCoreTyped (-80) depth.getNat with
  | .ok _ => pure ()
  | .error failure => throwError "Density cached sum certificate rejected: {repr failure}"
