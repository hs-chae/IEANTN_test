/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Tactic
noncomputable section
set_option autoImplicit false
namespace RH080Next.Primal

/-- Readable bounds derived from the first actual population numerical source. -/
def sparsePopulationLine (α : ℝ) : ℝ := 944247/1000000+(1163388/1000000)*α
/-- The zero-leakage constant-window profile, with strictly slack norm intercept. -/
def flatPopulationLine (α : ℝ) : ℝ := 9/8+(16/15)*α
/-- The asymptotic inversion of PrimeInterval.v4.optimized_strict_family's
leading count `(8/9)c-18203/20000`. The original theorem additionally has a
positive4.2/log(x) allowance, strict endpoints, x>=exp24, and1.03<=c<=16.
This scalar definition does not discard those conditions from that theorem. -/
def previousOcticPopulationLine (α : ℝ) : ℝ := (9/8)*(α+18203/20000)
/-- Best of the two newly verified-source profiles, not an overall optimum. -/
def newPopulationFrontier (α : ℝ) : ℝ :=
  min (sparsePopulationLine α) (flatPopulationLine α)

theorem sparse_line_lt_octic {α : ℝ} (hα : α≤2) :
    sparsePopulationLine α<previousOcticPopulationLine α := by
  unfold sparsePopulationLine previousOcticPopulationLine
  linarith

theorem flat_line_lt_octic {α : ℝ} (hα : 2≤α) :
    flatPopulationLine α<previousOcticPopulationLine α := by
  unfold flatPopulationLine previousOcticPopulationLine
  linarith

/-- Exact scalar improvement on the common asymptotic domain. This is not a
claim that the original explicit onsetexp24 transfers to the new profiles. -/
theorem new_frontier_lt_octic (α : ℝ) :
    newPopulationFrontier α<previousOcticPopulationLine α := by
  unfold newPopulationFrontier
  rcases le_total α 2 with h | h
  · exact (min_le_left _ _).trans_lt (sparse_line_lt_octic h)
  · exact (min_le_right _ _).trans_lt (flat_line_lt_octic h)

/-- Exact alpha range whose old scalar width lies inside the original theorem's
coefficient range; epsilon/strict limiting margins must be handled separately. -/
theorem previous_octic_width_domain (α : ℝ) :
    (103/100≤previousOcticPopulationLine α ∧ previousOcticPopulationLine α≤16) ↔
      (973/180000≤α ∧ α≤2396173/180000) := by
  unfold previousOcticPopulationLine
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

example : newPopulationFrontier 0=944247/1000000 := by norm_num [newPopulationFrontier,sparsePopulationLine,flatPopulationLine]
example : newPopulationFrontier (1/2)=1525941/1000000 := by norm_num [newPopulationFrontier,sparsePopulationLine,flatPopulationLine]
example : newPopulationFrontier 1=421527/200000 := by norm_num [newPopulationFrontier,sparsePopulationLine,flatPopulationLine]
example : newPopulationFrontier 2=391/120 := by norm_num [newPopulationFrontier,sparsePopulationLine,flatPopulationLine]
example : newPopulationFrontier 5=155/24 := by norm_num [newPopulationFrontier,sparsePopulationLine,flatPopulationLine]
example : newPopulationFrontier 10=283/24 := by norm_num [newPopulationFrontier,sparsePopulationLine,flatPopulationLine]

#print axioms new_frontier_lt_octic
#print axioms previous_octic_width_domain
end RH080Next.Primal
