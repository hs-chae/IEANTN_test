/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Tactic
namespace PVEvolutionA.Cumulative
/-- Each stage keeps all earlier allowances, including a stronger no-PV input.
An unavailable candidate is not assigned a fabricated value by this interface. -/
def stages (legacy noPV fixedPV evolved : ℝ) : Fin 4 → ℝ :=
  ![legacy,min legacy noPV,min (min legacy noPV) fixedPV,
    min (min (min legacy noPV) fixedPV) evolved]

theorem nested (a b c d : ℝ) :
    stages a b c d 3≤stages a b c d 2 ∧
    stages a b c d 2≤stages a b c d 1 ∧
    stages a b c d 1≤stages a b c d 0 :=
  ⟨min_le_left _ _,min_le_left _ _,min_le_left _ _⟩

theorem valid {e a b c d : ℝ} (ha:e≤a) (hb:e≤b) (hc:e≤c) (hd:e≤d) :
    ∀i, e≤stages a b c d i := by
  intro i
  fin_cases i
  · exact ha
  · exact le_min ha hb
  · exact le_min (le_min ha hb) hc
  · exact le_min (le_min (le_min ha hb) hc) hd
/-- If no-PV is strongest, evolution inherits it; it cannot claim a strict gain. -/
theorem noPV_dominates {a b c d : ℝ} (ha:b≤a) (hc:b≤c) (hd:b≤d) :
    stages a b c d 3=b := by
  change min (min (min a b) c) d=b
  rw [min_eq_right ha,min_eq_left hc,min_eq_left hd]
#print axioms nested
#print axioms valid
end PVEvolutionA.Cumulative
