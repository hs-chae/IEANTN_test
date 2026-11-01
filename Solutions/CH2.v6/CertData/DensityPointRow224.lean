/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityNumericDefs
set_option leancert.trust "kernel"
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityPointRow224

theorem endpoint_upper : Q (7/8) 67 ≤ (18473 : ℝ) / 2000000 := by
  dsimp only [Q]
  interval_decide <;> norm_num [LeanCert.Core.MathConst.toReal] at * <;> first | assumption | ring_nf at *

theorem base_upper : Real.exp (-(224 : ℝ)/8) *
    (((67 : ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi) + (2+1/Real.pi)*((67:ℝ)+(1:ℝ)/10^9)) ≤ (1 : ℝ) / 10000000 := by
  interval_decide <;> norm_num [LeanCert.Core.MathConst.toReal] at * <;> first | assumption | ring_nf at *

#print axioms endpoint_upper
#print axioms base_upper
end DensityPointRow224
