/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeWindows
namespace PrimeKernelInputs.v3
open Real Set IEANTN.PrimeWindows
def octic_215_explicit_formula : Prop := ExplicitFormula 4 (43/20)
def octic_family_explicit_formula : Prop := ∀ C ∈ Icc (103/100:ℝ) 16, ExplicitFormula 4 C
end PrimeKernelInputs.v3
