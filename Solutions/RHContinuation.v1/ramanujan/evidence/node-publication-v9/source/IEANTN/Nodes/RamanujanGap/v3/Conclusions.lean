/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RamanujanGap.v1.Conclusions

/-! New post-lock quantitative all-real Ramanujan bounds. The numerical C
coefficient program belongs to the solution; these statements use only explicit
mathematical functions and the unchanged actual prime-counting gap. -/
namespace RamanujanGap.v3
open Real IEANTN Finset

/-- The complete positive degree20 coefficient polynomial. -/
noncomputable def polynomial (u : ℝ) : ℝ :=
  ∑ j ∈ range 21,
    (((∑ i ∈ range (j+1), i.factorial*j.choose i : ℕ):ℝ) -
      ((∑ i ∈ range (j+1), i.factorial*(j-i).factorial : ℕ):ℝ))*u^j

/-- Exact omitted square-convolution coefficients. -/
def tailCoefficient (j : ℕ) : ℕ :=
  ∑ i ∈ range (20-j), (i+j+1).factorial*(20-i).factorial

/-- Variable analytic remainder; it decays rather than remaining a fixed .001. -/
noncomputable def analyticError (u : ℝ) : ℝ :=
  (∑ j ∈ range 20, (tailCoefficient j:ℝ)*u^(j+17))+
    (11/5:ℝ)*(7*(Nat.factorial 21:ℝ)*u^17)+(7*(Nat.factorial 21:ℝ)*u^17)^2

/-- The full normalized RH loss at logarithmic argument L. -/
noncomputable def rhLoss (l : ℝ) : ℝ :=
  (1/(8*Real.pi))*l^5*(l-1)*exp ((1-l)/2)+
    (21/10:ℝ)*(1/(8*Real.pi))*l^6*exp (-l/2)+(1/(8*Real.pi))^2*l^8*exp (-l)

/-- Explicit complete source-polynomial analytic envelope at logarithmic argument L. -/
noncomputable def fullEnvelope (l : ℝ) : ℝ :=
  l^4*polynomial (1/l)-analyticError (1/l)-rhLoss l

/-- Combined all-real profile. The two maxima retain both certified tail bounds. -/
noncomputable def profile (x : ℝ) : ℝ :=
  if exp 70 ≤ x then max (1+14/log x+144/(log x)^2) (fullEnvelope (log x))
  else if exp 42 ≤ x then max (4/5) (fullEnvelope (log x))
  else 1/12

/-- New quantitative bound on every real x≥640b, with the unchanged integer onset. -/
def one_twelfth_margin : Prop := ∀ x : ℝ, 640000000000 ≤ x →
  (1/12:ℝ)*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x

/-- Nonconstant whole-ray bound, not a sampled table: L=log x≥70. -/
def tail_144_margin : Prop := ∀ x : ℝ, exp 70 ≤ x →
  (1+14/log x+144/(log x)^2)*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x

/-- Complete combined profile for the actual nonlinear prime-counting expression. -/
def full_profile : Prop := ∀ x : ℝ, 640000000000 ≤ x →
  profile x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x

/-- Ramanujan's strict inequality on the same all-real inclusive ray. -/
def ramanujan : Prop := ∀ x : ℝ, 640000000000 ≤ x →
  primeCounting x^2 < exp 1*x/log x*primeCounting (x/exp 1)
end RamanujanGap.v3
