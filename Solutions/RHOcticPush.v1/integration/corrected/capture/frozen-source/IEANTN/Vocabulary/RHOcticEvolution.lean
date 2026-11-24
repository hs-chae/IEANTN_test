/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHSmoothing

/-! Shared evolved box envelope. Definitions only. Exact Mellin identities and
infinite-zero/explicit-formula assumptions remain statements in their own nodes. -/
namespace IEANTN.RHOcticEvolution
/-- Same box geometry and zero allowances, with the source-reused improved moment cap. -/
noncomputable def boxBound (L : ℝ) : ℝ :=
  IEANTN.RHSmoothing.envelope (Real.log 2) (70871 / 100000) L
end IEANTN.RHOcticEvolution
