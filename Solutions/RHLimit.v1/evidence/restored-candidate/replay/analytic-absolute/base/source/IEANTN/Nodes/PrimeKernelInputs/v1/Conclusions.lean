/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeWindows
namespace PrimeKernelInputs.v1
open Real Set IEANTN.PrimeWindows
/-- Six actual analytic/geometric obligations for the width2.15 octic window.
None asserts the desired prime-count inequality. Written proofs and quadrature
receipts exist; the full analytic contract is not Lean closed. -/
def octic_215 : Prop := ExplicitFormula 4 (43 / 20) ∧
  ZeroEstimate 4 (43 / 20) (911 / 500) (3 / 2) (3 / 125) ∧
  PrimePowerCost 4 (43 / 20) (31 / 2000) ∧ TrivialCost 4 (43 / 20) (1 / 1000) ∧
  ScalarGeometry 4 (43 / 20) (911 / 500) (3 / 2)
    (3 / 125) (31 / 2000) (1 / 1000) (29 / 5) ∧ ForwardCoverage (43 / 20)
/-- Uniform contracts for the actual all-real width/count frontier. -/
def octic_family : Prop := ∀ C ∈ Icc (103 / 100 : ℝ) 16,
  ExplicitFormula 4 C ∧ ZeroEstimate 4 C (911 / 500) (3 / 2) (3 / 20) ∧
  PrimePowerCost 4 C (29 / 500) ∧ TrivialCost 4 C (1 / 1000) ∧
  ScalarGeometry 4 C (911 / 500) (3 / 2)
    (3 / 20) (29 / 500) (1 / 1000) (21 / 5) ∧ ForwardCoverage C
end PrimeKernelInputs.v1
