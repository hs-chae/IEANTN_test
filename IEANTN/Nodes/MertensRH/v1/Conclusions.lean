/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.SignedArithmetic
import IEANTN.Nodes.RH.v1.Conclusions
import IEANTN.Nodes.Buthe.v1.Conclusions

/-! Signed first-Mertens bounds, retaining square and cube prime-power tails.
The five original source inputs are explicit and are unchanged by the gain. -/
namespace MertensRH.v1
open IEANTN.SignedArithmetic
/-- BFKNW2608.01498v1 Proposition29(ii), Eq(154), x>=2. -/
def bfknw154 : Prop := ∀ x : ℝ, 2 ≤ x →
  |CA x - Real.log x + Real.eulerMascheroniConstant| ≤
    |Chebyshev.psi x - x| / x + J1 x + Real.log (2 * Real.pi) / x
/-- BFKNW Lemma21, Eq(85)-(90), full both-sign ordinate mass with actual
multiplicity. The numerical source remains literature-backed, not recomputed. -/
def bfknw21 : Prop := Summable reciprocalWeight ∧ reciprocalMass ≤ 0.04620999
/-- New same-five-input improvement from .006 to .014 on the entire old band.
This is the prime sum A, not the summatory Mobius function M. -/
def positive_cube : Prop := ∀ x : ℝ, Real.exp 24 ≤ x → x ≤ (10 : ℝ)^19 →
  0.014 / Real.sqrt x < A x - Real.log x - E
/-- A different Pareto point: onset exp21, margin .00031/sqrtx. -/
def positive_earlier : Prop := ∀ x : ℝ, Real.exp 21 ≤ x → x ≤ (10 : ℝ)^19 →
  0.00031 / Real.sqrt x < A x - Real.log x - E
/-- The retained nonconstant cube-tail profile, with x=u^12.
Its full real domain is proved, rather than sampled. -/
def cube_profile : Prop := ∀ u : ℝ, 7 ≤ u → u^12 ≤ (10 : ℝ)^19 →
  0.01379001 + ((1/2:ℝ)/u^2-2.55/u^3-2.29/u^4-2.5/u^6) -
    2*u^6/(10:ℝ)^19 ≤ u^6*(A (u^12)-Real.log (u^12)-E)
end MertensRH.v1
