/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.FapFourierNorm.v1.Tables

/-! Data-only reuse of the original locked Fap profile; no duplicate input,
new witness, source output or proof declaration is introduced. -/
namespace FapFourierNorm.v2.Tables
abbrev affineNodes : List ℚ := FapFourierNorm.v1.Tables.affineNodes
end FapFourierNorm.v2.Tables
