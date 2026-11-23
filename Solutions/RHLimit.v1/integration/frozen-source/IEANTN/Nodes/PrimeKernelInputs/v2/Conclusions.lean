/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeWindows
namespace PrimeKernelInputs.v2
open Real Set IEANTN.PrimeWindows
def octic_215_explicit_formula : Prop := ExplicitFormula 4 (43/20)
def octic_215_zero_estimate : Prop := ZeroEstimate 4 (43/20) (911/500) (3/2) (3/125)
def octic_family_explicit_formula : Prop := ∀ C ∈ Icc (103/100:ℝ) 16, ExplicitFormula 4 C
def octic_family_zero_estimate : Prop := ∀ C ∈ Icc (103/100:ℝ) 16,
  ZeroEstimate 4 C (911/500) (3/2) (3/20)
end PrimeKernelInputs.v2
