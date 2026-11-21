/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Zeta
import IEANTN.Vocabulary.ZeroFreeHalfPlane

/-! # RH.v1: an explicit shared hypothesis and its logical interfaces

The `hypothesis` leaf is conditional experimental input, never a proof of RH.
The logical consequences are recorded separately in `RHAdapters.v1`. The exact
Mathlib definition excludes the negative even integers and the pole at 1.
These claims concern zero locations only and carry no numerical zero data.
-/
namespace RH.v1

/-- The shared, unproved Riemann hypothesis, exactly as defined by pinned Mathlib. -/
def hypothesis : Prop := RiemannHypothesis

end RH.v1
