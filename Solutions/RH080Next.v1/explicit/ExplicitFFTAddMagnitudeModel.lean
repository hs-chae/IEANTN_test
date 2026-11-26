/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTMagnitudeInto
import FFTProductBindings
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddMagnitudeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs

def base : Nat:=1000000000
structure Layout where
  outObject : Nat
  aObject : Nat
  length : Nat → Nat
  outStart : Nat
  aStart : Nat
  n : Nat
  outBound : outStart+n≤length outObject
  aBound : aStart+5≤length aObject
  safe : outObject≠aObject ∨ outStart+n≤aStart ∨ aStart+5≤outStart
  small : n≤6
structure Input where
  layout : Layout
  old : Nat → Nat → Nat
  outDigits : ∀j<layout.n,old layout.outObject (layout.outStart+j)<base
  aDigits : ∀j<5,old layout.aObject (layout.aStart+j)<base

def aDigit (input : Input) (j : Nat) : Nat:=if j<5 then input.old input.layout.aObject (input.layout.aStart+j) else 0

def row (input : Input) (j : Nat) : (Nat → Nat)×Nat:=addDigits base
  (fun k=>input.old input.layout.outObject (input.layout.outStart+k)) (aDigit input) j

def currentData (input : Input) : Nat → Nat → Nat
  | 0=>input.old input.layout.outObject
  | j+1=>Function.update (currentData input j) (input.layout.outStart+j)
      ((input.old input.layout.outObject (input.layout.outStart+j)+aDigit input j+(row input j).2)%base)

theorem aDigit_bound (input : Input) (j : Nat) : aDigit input j<base:=by
  unfold aDigit;split_ifs with h
  · exact input.aDigits j h
  · norm_num [base]

theorem row_carry (input : Input) (j : Nat) (hj : j≤ input.layout.n) : (row input j).2≤1:=by
  induction j with
  | zero=>simp [row,addDigits]
  | succ j ih=>
    have hsum : input.old input.layout.outObject (input.layout.outStart+j)+aDigit input j+(row input j).2<2*base:=by
      have ho:=input.outDigits j (by omega);have ha:=aDigit_bound input j;have hc:=ih (by omega);omega
    have q:=(Nat.div_lt_iff_lt_mul (show 0<base by norm_num [base])).mpr hsum
    change (input.old input.layout.outObject (input.layout.outStart+j)+aDigit input j+(row input j).2)/base≤1
    omega

theorem currentData_unread (input : Input) (j k : Nat) (hk : j≤k) :
    currentData input j (input.layout.outStart+k)=input.old input.layout.outObject (input.layout.outStart+k):=by
  induction j with
  | zero=>rfl
  | succ j ih=>
    rw [currentData,Function.update_of_ne (show input.layout.outStart+k≠input.layout.outStart+j by omega)]
    exact ih (by omega)

theorem currentData_outside (input : Input) (j k : Nat) (outside : k< input.layout.outStart ∨ input.layout.outStart+j≤k) :
    currentData input j k=input.old input.layout.outObject k:=by
  induction j with
  | zero=>rfl
  | succ j ih=>
    rw [currentData,Function.update_of_ne (show k≠input.layout.outStart+j by omega)]
    exact ih (by omega)

theorem currentData_processed (input : Input) (j k : Nat) (hk : k<j) :
    currentData input j (input.layout.outStart+k)=(row input j).1 k:=by
  induction j with
  | zero=>omega
  | succ j ih=>
    by_cases same : k=j
    · subst k;simp [currentData,row,addDigits]
    · simp only [currentData,Function.update_of_ne (show input.layout.outStart+k≠input.layout.outStart+j by omega)]
      change _=(Function.update (row input j).1 j _) k
      rw [Function.update_of_ne same]
      exact ih (by omega)

theorem result_conservation (input : Input) :
    magnitude base input.layout.n (fun j=>currentData input input.layout.n (input.layout.outStart+j))+
      (row input input.layout.n).2*base^input.layout.n=
      magnitude base input.layout.n (fun j=>input.old input.layout.outObject (input.layout.outStart+j))+
      magnitude base input.layout.n (aDigit input):=by
  have eqDigits : magnitude base input.layout.n (fun j=>currentData input input.layout.n (input.layout.outStart+j))=
      magnitude base input.layout.n (row input input.layout.n).1:=by
    apply Finset.sum_congr rfl
    intro j hj
    change currentData input input.layout.n (input.layout.outStart+j)*_=_
    rw [currentData_processed input _ j (Finset.mem_range.mp hj)]
  rw [eqDigits]
  exact addDigits_value _ _ _ _

#print axioms row_carry
#print axioms result_conservation
end RH080Next.FFTPV.AddMagnitudeSource
