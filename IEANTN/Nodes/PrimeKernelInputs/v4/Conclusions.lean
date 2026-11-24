/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeWindows
namespace PrimeKernelInputs.v4
open Real Set IEANTN.PrimeWindows
/-- Exact original fixed2.15 infinite-zero target; now derived, not assumed. -/
def octic_215_zero_estimate : Prop := ZeroEstimate 4 (43/20) (911/500) (3/2) (3/125)
/-- Exact original full-domain infinite-zero target. -/
def octic_family_zero_estimate : Prop := ∀ C ∈ Icc (103/100:ℝ) 16,
  ZeroEstimate 4 C (911/500) (3/2) (3/20)
/-- Stronger fixed estimate from the very same7301-row kernel certificate. -/
def optimized_215_zero_estimate : Prop :=
  ZeroEstimate 4 (43/20) (18203/10000) (1457/1000) (3/125)
/-- Stronger estimate over every real C in the original complete domain. -/
def optimized_family_zero_estimate : Prop := ∀ C ∈ Icc (103/100:ℝ) 16,
  ZeroEstimate 4 C (18203/10000) (1457/1000) (3/20)
end PrimeKernelInputs.v4
