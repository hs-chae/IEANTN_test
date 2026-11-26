/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace RH080Next.PopulationEnvelope

def w4 (α : ℝ) : ℝ := 170212349/200000000+(1505657839/1000000000)*α
def sparse (α : ℝ) : ℝ := 944247/1000000+(1163388/1000000)*α
def flat (α : ℝ) : ℝ := 9/8+(16/15)*α
def paperFirst (α : ℝ) : ℝ := 851127043/1000000000+(1505827/1000000)*α
def paperSecond (α : ℝ) : ℝ := 85124642/100000000+(1505237/1000000)*α

theorem w4_lt_paperFirst (α : ℝ) (hα : 0≤α) : w4 α<paperFirst α := by
  dsimp [w4,paperFirst]
  nlinarith

/-- The two actually constructed curves together beat both printed BRv2
population lines at every nonnegative density. No assertion about other
published bounds, optimality or a numerical onset is made. -/
theorem two_curve_lt_printed_minimum (α : ℝ) (hα : 0≤α) :
    min (w4 α) (sparse α)<min (paperFirst α) (paperSecond α) := by
  apply lt_min
  · exact (min_le_left _ _).trans_lt (w4_lt_paperFirst α hα)
  · by_cases small : α≤1/3
    · apply (min_le_left _ _).trans_lt
      dsimp [w4,paperSecond]
      nlinarith
    · apply (min_le_right _ _).trans_lt
      dsimp [sparse,paperSecond]
      have large : 1/3<α := lt_of_not_ge small
      nlinarith

/-- Adding the flat provider preserves the strict comparison. -/
theorem three_curve_lt_printed_minimum (α : ℝ) (hα : 0≤α) :
    min (w4 α) (min (sparse α) (flat α))<min (paperFirst α) (paperSecond α) := by
  have le : min (w4 α) (min (sparse α) (flat α))≤min (w4 α) (sparse α) := by
    exact le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
  exact le.trans_lt (two_curve_lt_printed_minimum α hα)

#print axioms w4_lt_paperFirst
#print axioms two_curve_lt_printed_minimum
#print axioms three_curve_lt_printed_minimum
end RH080Next.PopulationEnvelope
