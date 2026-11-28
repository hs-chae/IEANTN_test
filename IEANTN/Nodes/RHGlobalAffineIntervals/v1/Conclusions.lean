/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHFiniteAffineIntervals.v2.Conclusions
noncomputable section
open Real
namespace RHGlobalAffineIntervals.v1

def piecewiseWidth (x : ℝ) : ℝ :=
  if x<11 then 777/1000 else if x≤exp 63 then 37/50 else
    if x≤exp 70 then 3/4 else if x≤exp 174 then 4/5 else 425531/500000

/-- Every real x>=4 has a prime strictly inside the original global0.851062
interval. Named analytic, historical finite-gap and RH inputs stay explicit. -/
def global_0851062 : Prop := ∀x:ℝ,4≤x→∃p:ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧
  (p:ℝ)<x+(425531/500000:ℝ)*sqrt x*log x
/-- Exact first piece:4<=x<11, strict prime endpoints, coefficient0.777. -/
def branch_0777 : Prop := RHFiniteAffineIntervals.v2.interval_0777_small
/-- Exact second piece:11<=x<=exp63; equality belongs to this branch. -/
def branch_074 : Prop := RHFiniteAffineIntervals.v2.interval_074_full
/-- Exact third piece:exp63<x<=exp70, with both prime endpoints strict. -/
def branch_075 : Prop := ∀x:ℝ,exp 63<x→x≤exp 70→∃p:ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧
  (p:ℝ)<x+(3/4:ℝ)*sqrt x*log x
/-- Exact fourth piece:exp70<x<=exp174, with both prime endpoints strict. -/
def branch_08 : Prop := ∀x:ℝ,exp 70<x→x≤exp 174→∃p:ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧
  (p:ℝ)<x+(4/5:ℝ)*sqrt x*log x
/-- Exact final piece:exp174<x, retaining the original global coefficient. -/
def branch_0851062 : Prop := ∀x:ℝ,exp 174<x→∃p:ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧
  (p:ℝ)<x+(425531/500000:ℝ)*sqrt x*log x
/-- Complete five-piece theorem, without a gap or endpoint rounding. -/
def piecewise_strict : Prop := ∀x:ℝ,4≤x→∃p:ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧
  (p:ℝ)<x+piecewiseWidth x*sqrt x*log x
end RHGlobalAffineIntervals.v1
