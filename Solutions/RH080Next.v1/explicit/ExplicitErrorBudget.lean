/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitMVConstants
import ExplicitCentralPrimes

set_option autoImplicit false
noncomputable section
open Real
namespace RH080Next.Explicit

def explicitPenalty : ℝ := 400001/100000

def explicitConstant (c J H S k : ℝ) : ℝ :=
  S+explicitPenalty*J*c*log k/mvBlockDenom k 42+
    2*explicitPenalty*H/(k*mvBlockDenom k 42)+(3/2500:ℝ)

/-- Assembly of the unchanged 0.0012 budget. The two inequalities here are
application lemmas for the ACTUAL Mangoldt and prime decomposition, not new
analytic source predicates: the complete consumer supplies them from the
proved Mellin/zero/pole/trivial/MV/prime-power paths. The only loss in this
last algebra is at most 2e-6 from the proved pole-scale linearization. -/
theorem explicit_budget_assembly (c t F0 J H U S k P A C powers : ℝ)
    (hD0 : 0 ≤ F0-explicitPenalty*J) (hD2 : F0-explicitPenalty*J ≤ 2)
    (hP : c*t/2-(1/1000000:ℝ) ≤ P)
    (hMellin : P*F0-U*(t/2-log (c*t/2))-S-(11/100000:ℝ) < A)
    (hArithmetic : A ≤ C+explicitPenalty*P*J+
      explicitPenalty*J*c*log k/mvBlockDenom k 42+
      2*explicitPenalty*H/(k*mvBlockDenom k 42)+powers)
    (hPowers : powers < (1/1000:ℝ)) :
    explicitResidual c (F0-explicitPenalty*J) U (explicitConstant c J H S k) t < C := by
  have hlin := mul_le_mul_of_nonneg_right hP hD0
  have hDerr : (F0-explicitPenalty*J)/1000000 ≤ (2/1000000:ℝ) := by linarith
  unfold explicitResidual explicitConstant
  nlinarith

#print axioms explicit_budget_assembly
end RH080Next.Explicit
