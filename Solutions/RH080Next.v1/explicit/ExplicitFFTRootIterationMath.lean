/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootIterExpressions
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RH080Next.FFTPV.RootSource
open FFT.IntegerModel
open IncrementSource (base)

def cosineProduct (n j : Nat) : Int:=((taylorState n j).ct*x2Integer n)/unit

def sineProduct (n j : Nat) : Int:=((taylorState n j).st*x2Integer n)/unit

def nextCosineTerm (n j : Nat) : Int:=cosineProduct n j/((2*(j+1)*(2*(j+1)-1):Nat):Int)

def nextSineTerm (n j : Nat) : Int:=sineProduct n j/((2*(j+1)*(2*(j+1)+1):Nat):Int)

theorem next_ct (n j : Nat) : (taylorState n (j+1)).ct=nextCosineTerm n j := by
  simp only [taylorState,taylorStep,nextCosineTerm,cosineProduct]
  split_ifs <;> rfl

theorem next_st (n j : Nat) : (taylorState n (j+1)).st=nextSineTerm n j := by
  simp only [taylorState,taylorStep,nextSineTerm,sineProduct]
  split_ifs <;> rfl

theorem next_cr (n j : Nat) : (taylorState n (j+1)).cr=
    if 0<(j+1)%2 then (taylorState n j).cr-nextCosineTerm n j
    else (taylorState n j).cr+nextCosineTerm n j := by
  have parity : (j+1)%2=0 ∨ (j+1)%2=1:=by have h:=Nat.mod_lt (j+1) (show 0<2 by omega);omega
  rcases parity with even|odd
  · simp [taylorState,taylorStep,even,nextCosineTerm,cosineProduct]
  · simp [taylorState,taylorStep,odd,nextCosineTerm,cosineProduct]

theorem next_sr (n j : Nat) : (taylorState n (j+1)).sr=
    if 0<(j+1)%2 then (taylorState n j).sr-nextSineTerm n j
    else (taylorState n j).sr+nextSineTerm n j := by
  have parity : (j+1)%2=0 ∨ (j+1)%2=1:=by have h:=Nat.mod_lt (j+1) (show 0<2 by omega);omega
  rcases parity with even|odd
  · simp [taylorState,taylorStep,even,nextSineTerm,sineProduct]
  · simp [taylorState,taylorStep,odd,nextSineTerm,sineProduct]

/-- Exact finite source guard bounds for the unchanged two original grids.
The products are intermediate source values, not supplied output certificates. -/
theorem original_intermediate_bounds (n j : Nat) (grid : OriginalGrid n) (hj : j<10) :
    0≤ cosineProduct n j ∧ (cosineProduct n j).natAbs≤1000*10^36 ∧
    0≤ sineProduct n j ∧ (sineProduct n j).natAbs≤1000*10^36 ∧
    (taylorState n j).ct.natAbs≤1000*10^36 ∧ (taylorState n j).st.natAbs≤1000*10^36 ∧
    (x2Integer n).natAbs≤1000*10^36 ∧
    (taylorState n j).cr.natAbs+(nextCosineTerm n j).natAbs< base^5 ∧
    (taylorState n j).sr.natAbs+(nextSineTerm n j).natAbs< base^5 := by
  rcases grid with rfl|rfl
  all_goals interval_cases j <;> decide

#print axioms next_cr
#print axioms next_sr
#print axioms original_intermediate_bounds
end RH080Next.FFTPV.RootSource
