/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.BoxMellinInputs.v1.Conclusions
namespace BoxMellinInputs.v2
/-- The exact original first moment, including actual integrability, now proved unconditionally. -/
def first_moment : Prop := BoxMellinInputs.v1.first_moment
/-- The exact original J1 identity, with original actualq and canonicalgamma1, now proved. -/
def second_moment_identity : Prop := BoxMellinInputs.v1.second_moment_identity
/-- The original unconditional canonical-sequence/trapezoid theorem, preserved exactly. -/
def stieltjes_trapezoid : Prop := BoxMellinInputs.v1.stieltjes_trapezoid
end BoxMellinInputs.v2
