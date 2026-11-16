/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Basic.Real.Basic

/-! Rounded coefficients certified by outward-rounded arithmetic in NumericalCertificate.json.
These are new derivation data, not numbers printed by Chirre–Helfgott. -/

namespace CH2.v6

/-- `(log x₀, C)` means the proposed analytic transfer gives `Eψ x ≤ C x^(-1/8)` for `x ≥ x₀`.
All endpoints are included; the written proof controls the full ray above each threshold. -/
def densityFrontier : List (ℝ × ℝ) :=
  [
  (64, 0.97500),
  (80, 0.23719),
  (96, 0.08349),
  (112, 0.04372),
  (128, 0.03013),
  (160, 0.02069),
  (192, 0.01713),
  (224, 0.01526),
  (256, 0.01411),
  (300, 0.01310),
  (512, 0.01117),
  (1000, 0.01014)
]

end CH2.v6
