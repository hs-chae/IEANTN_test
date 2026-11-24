/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.GreenSmooth
namespace GreenSmooth.v1
open IEANTN.GreenSmooth MeasureTheory
open scoped ContDiff
/-- Green Definition7.1/Theorem7.1, printed40; absolute convergence uses
Lemma7.1, printed43–44. This is a genuine general literature input. -/
def formula : Prop :=
  ∀ W : ℝ → ℝ, ContDiff ℝ ∞ W → HasCompactSupport W →
    Function.support W ⊆ Set.Ici 1 → ∀ X : ℝ, 1 < X →
      Summable (sourcePacket W X) ∧
        (((∑' k : ℕ, (ArithmeticFunction.vonMangoldt k : ℝ) * W ((k : ℝ) / X)) : ℝ) : ℂ) =
          ((X * ∫ t : ℝ, W t : ℝ) : ℂ) - ∑' z : ProperZero, sourcePacket W X z
end GreenSmooth.v1
