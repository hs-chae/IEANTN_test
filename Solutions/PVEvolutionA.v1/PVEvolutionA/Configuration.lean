/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Separated
namespace PVEvolutionA.Configuration
open WinnerProgramA
/-- The CLI and each finite proof use these same expression generators and caps. -/
def program : Fin 3 → List Row :=
  ![Separated.program 300 100 65536,
    Separated.program 330 100 65536,
    Separated.program (661/2) 100 65536]
def bounds : Fin 3 → List ℚ :=
  ![[3/1000000000000,9468285634/1000000000000],
    [3/1000000000000,9150520019/1000000000000],
    [3/1000000000000,9145877460/1000000000000]]
/-- Explicit last-entry reduction for the canonical rc2 simplifier. This adds
only a proof lemma; program generation and literal numerical data are unchanged. -/
@[simp] theorem fin3_last {α:Type*} (a b c:α) : (![a,b,c] : Fin 3→α) 2=c := rfl
end PVEvolutionA.Configuration
