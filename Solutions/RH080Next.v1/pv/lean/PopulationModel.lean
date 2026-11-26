/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SineSpec
import AngleFolding
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.PopulationPV.Model

/-- Exact input packet; these are input coefficients, not claimed outputs. -/
def coefficients : List Nat := [546871713113309800,546871713113309600,
  546871713113309600,546871713113309600,546871713113309600,
  546871713113309600,515419762691595100,357059942573668200,
  119725872611533800,0,0,0,0,0,0,0]
def coefficient (j : Nat) : Nat := coefficients.getD j 0
def weight (j : Nat) : Nat := if j=0 then 1 else 2
def sineFixed := RH080.SineBridge.sineFixed
def folded (j k : Nat) := RH080.SineBridge.foldAngle (2*j*k+128)
def splitProduct (a s : Nat) : Nat :=
  a/1000000000*s+(a%1000000000*s)/1000000000

def pointStep (k : Nat) (state : Nat×Nat) (j : Nat) : Nat×Nat :=
  let term := weight j * splitProduct (coefficient j) (sineFixed (folded j k).1)
  if (folded j k).2 then (state.1,state.2+term)
  else (state.1+term,state.2)

def rawSample (k : Nat) : Nat×Nat := (List.range 16).foldl (pointStep k) (0,0)
def sampleUpper (k : Nat) : Nat :=
  let p := rawSample k
  (if p.2≤p.1 then p.1-p.2 else p.2-p.1)+100000000000000

def chordTerm (j : Nat) : Nat :=
  let a := coefficient j
  let factor := 20*j*j
  a/196608*factor+(a%196608*factor+196608-1)/196608

def chordUpper : Nat := ((List.range 16).map chordTerm).sum

def normUpper : Nat :=
  ((List.range 256).map fun k => (sampleUpper k+255)/256).sum+chordUpper

noncomputable def trigPolynomial (y : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 16,
    ((weight j*coefficient j : Nat) : ℝ) *
      Real.cos (2*Real.pi*j*y))/1000000000000000000

noncomputable def signedTerm (j k : Nat) : ℝ :=
  let term := (weight j*splitProduct (coefficient j) (sineFixed (folded j k).1) : Nat)
  if (folded j k).2 then -(term : ℝ) else (term : ℝ)

theorem coefficients_fit (j : Fin 16) : coefficient j.val ≤ 1000000000000000000 := by
  fin_cases j <;> decide +kernel

theorem weights_fit (j : Nat) : weight j ≤ 2 := by
  unfold weight
  split <;> omega

theorem normUpper_exact : normUpper = 887721072633027910 := by decide +kernel

theorem sineFixed_fits (r : Fin 129) : sineFixed r.val ≤ 1000000010 := by
  fin_cases r <;> decide +kernel

#print axioms normUpper_exact
#print axioms coefficients_fit
#print axioms sineFixed_fits
end RH080Next.PopulationPV.Model
