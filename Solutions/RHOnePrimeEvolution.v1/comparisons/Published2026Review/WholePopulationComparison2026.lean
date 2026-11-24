/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib

/-! Exact comparison of DISPLAYED population-width upper-bound curves.
Primary: Rafael Blanquer Robles, version2(21November2026), Theorem2 Eq(2),p2;
Section3 final paragraph,p10: moduli1,2 require ordinary RH only.
https://zenodo.org/records/24429650

This is algebra, not a proof of any analytic source predicate, liminf theorem,
optimality, novelty or attained infimum. The octic all-real theorem still needs
its actual[1.03,16] width domain and positive extra margin for strictliminf>α.
No standalone Blueprint label exists for this new comparison.
-/
noncomputable section
namespace RHOnePrime.Published2026Comparison

def octicWidthBound (α : ℝ) : ℝ := 163827 / 160000 + (9 / 8) * α
def paperWidthBound1 (α : ℝ) : ℝ := 851127043 / 1000000000 + (1505827 / 1000000) * α
def paperWidthBound2 (α : ℝ) : ℝ := 42562321 / 50000000 + (1505237 / 1000000) * α
def paperEnvelope (α : ℝ) : ℝ := min (paperWidthBound1 α) (paperWidthBound2 α)

theorem displayed_curve_iff (α : ℝ) :
    octicWidthBound α < paperEnvelope α ↔ 17267233 / 38023700 < α := by
  unfold octicWidthBound paperEnvelope paperWidthBound1 paperWidthBound2
  constructor
  · intro h
    have h2 := h.trans_le (min_le_right
      (851127043 / 1000000000 + (1505827 / 1000000) * α)
      (42562321 / 50000000 + (1505237 / 1000000) * α))
    linarith
  · intro h
    apply lt_min <;> linarith

/-- Restriction to the actual nonnegative-density parameter domain of Theorem2.
Only the two printed curves are compared; no analytic conclusion is imported. -/
theorem nonnegative_density_curve_iff {α : ℝ} (_hα : 0 ≤ α) :
    octicWidthBound α < paperEnvelope α ↔ 17267233 / 38023700 < α :=
  displayed_curve_iff α

theorem active_paper_branch (α : ℝ) :
    paperWidthBound2 α ≤ paperWidthBound1 α ↔ 119377 / 590000 ≤ α := by
  unfold paperWidthBound1 paperWidthBound2
  constructor <;> intro h <;> linarith

theorem exact_alpha_one :
    octicWidthBound 1 = (343827 / 160000 : ℝ) ∧
    paperEnvelope 1 = (117824171 / 50000000 : ℝ) ∧
    octicWidthBound 1 < paperEnvelope 1 := by
  norm_num [octicWidthBound, paperEnvelope, paperWidthBound1, paperWidthBound2]

/-- The displayed zero-density endpoint favors the new published curve.
This does not instantiate the octic family outside its actual width domain. -/
theorem exact_alpha_zero :
    paperEnvelope 0 = (851127043 / 1000000000 : ℝ) ∧
    paperEnvelope 0 < octicWidthBound 0 := by
  norm_num [octicWidthBound, paperEnvelope, paperWidthBound1, paperWidthBound2]

#print axioms displayed_curve_iff
#print axioms nonnegative_density_curve_iff
#print axioms active_paper_branch
#print axioms exact_alpha_one
#print axioms exact_alpha_zero
end RHOnePrime.Published2026Comparison
