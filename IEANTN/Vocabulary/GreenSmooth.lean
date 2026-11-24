/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHSmoothing
import Mathlib.Analysis.Calculus.ContDiff.Defs
namespace IEANTN.GreenSmooth
open MeasureTheory
open scoped ContDiff
def ProperZero := {z : ℂ // z ≠ 1 ∧ riemannZeta z = 0}
noncomputable def mellin (W : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), (W t : ℂ) * (t : ℂ) ^ s / (t : ℂ)
noncomputable def sourcePacket (W : ℝ → ℝ) (X : ℝ) (z : ProperZero) : ℂ :=
  (IEANTN.zetaOrder z.val : ℂ) * (X : ℂ) ^ z.val * mellin W z.val
end IEANTN.GreenSmooth
