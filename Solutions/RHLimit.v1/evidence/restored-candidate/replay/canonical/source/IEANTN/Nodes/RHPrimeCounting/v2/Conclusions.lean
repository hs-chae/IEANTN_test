/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHPrimeCounting.v1.Conclusions
import IEANTN.Vocabulary.ErrorTerms
namespace RHPrimeCounting.v2
open Real IEANTN
noncomputable def correction (L : ℝ) : ℝ :=
  2*log 4+(693/5000:ℝ)/(L-6)+L/(2*exp (L/4))+
    L*log (L/log 2)/exp (L/6)+(411/25:ℝ)*L/exp (L/2)
noncomputable def refinedCorrection (x : ℝ) : ℝ :=
  361/25+(693/5000:ℝ)*sqrt x/(log x*(log x-6))
def elementary_prime_powers : Prop := ∀ L : ℝ, 2 ≤ L →
  riemannPrimeCounting (exp L)-primeCounting (exp L) ≤
    2*log 4*exp (L/2)/L+exp (L/4)/2+exp (L/3)*log (L/log 2)
def refined_transfer : Prop := ∀ x : ℝ, exp 12 ≤ x →
  |riemannPrimeCounting x-li x-(Chebyshev.psi x-x)/log x| ≤ refinedCorrection x
def transfer_gain : Prop := ∀ x : ℝ, exp 16 ≤ x →
  (1/5:ℝ) < RHPrimeCounting.v1.transferCorrection x-refinedCorrection x
def ch_Epi : Prop := ∀ L : ℝ, 34 ≤ L →
  Eπ (exp L) ≤ (RHSmoothing.chBound L+correction L)*exp (-L/2)
def box_Epi : Prop := ∀ L : ℝ, 35 ≤ L →
  Eπ (exp L) ≤ (RHSmoothing.fastBound L+correction L)*exp (-L/2)
def ch_classical_gain : Prop := ∀ L : ℝ, 100 ≤ L →
  |primeCounting (exp L)-Li (exp L)| < exp (L/2)*(L/(8*π)-1/3)
def box_point_100 : Prop := Eπ (exp 100) < (357041/1000:ℝ)*exp (-50)
end RHPrimeCounting.v2
