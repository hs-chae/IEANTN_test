/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityFinSum
import LeanCert.Tactic.IntervalAuto.PointIneq

set_option leancert.trust "kernel"
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

open Lean Elab Tactic
/-- Use the pinned checker with a deeper enclosure; verification remains strictly kernel-only. -/
elab "density_finsum" depth:num : tactic => do
  match ← LeanCert.Tactic.Density.finSumBoundCoreTyped (-80) depth.getNat with
  | .ok _ => pure ()
  | .error failure => throwError "Density sum certificate rejected: {repr failure}"

namespace DensityNumeric
noncomputable def Q (s tau : ℝ) : ℝ :=
  let h := Real.log (3000000000000 : ℝ)
  let r := (8 * s - 5) / 3
  let q := 5 - 2 * s
  let p := 1 + q / (r * h) + q * (q - 1) / (r * h)^2 +
    q * (q - 1) * (q - 2) / (r * h)^3 + q * (q - 1) * (q - 2) * (q - 3) / (r * h)^4
  2 * (9.795 * Real.exp (-r * h + q * Real.log h) * p / r +
    4.465 * (h^2 + 2*h + 2) / 3000000000000) +
    4 * Real.pi * (9.795 * Real.exp (-r*tau + q*Real.log tau) + 4.465*tau^2*Real.exp (-tau))


end DensityNumeric
