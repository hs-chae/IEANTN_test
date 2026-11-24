/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHSmoothingInputs.v1.Conclusions
namespace RHSmoothingInputs.v2
/-- The exact original unconditional full Box explicit formula, now derived
from the genuine general integrated-Perron literature input. -/
def box_explicit_formula : Prop := RHSmoothingInputs.v1.box_explicit_formula
/-- The exact original RH Box zero estimate, with complete all-zero and moment
transport proved from the general Nicolas and BPT source inputs. -/
def box_zero_estimate : Prop := RHSmoothingInputs.v1.box_zero_estimate
end RHSmoothingInputs.v2
