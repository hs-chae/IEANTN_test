/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTIncrementSource
import FFTLimbDivision
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DivideSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def division (old : Nat → Nat) (start n d j : Nat) : (Nat → Nat) × Nat :=
  divideDigits base d (fun k=>old (start+j+k)) (n-j)

def currentData (old : Nat → Nat) (start n d j i : Nat) : Nat :=
  if start+j ≤ i ∧ i < start+n then (division old start n d j).1 (i-(start+j)) else old i

theorem currentData_initial (old : Nat → Nat) (start n d : Nat) : currentData old start n d n=old := by
  funext i
  simp [currentData]

theorem division_initial (old : Nat → Nat) (start n d : Nat) : (division old start n d n).2=0 := by
  simp [division,divideDigits]

theorem currentData_unread (old : Nat → Nat) (start n d j : Nat) :
    currentData old start n d (j+1) (start+j)=old (start+j) := by
  simp [currentData]

theorem division_step (old : Nat → Nat) (start n d j : Nat) (hj : j < n) :
    division old start n d j=
      (prependDigit (((division old start n d (j+1)).2*base+old (start+j))/d)
        (division old start n d (j+1)).1,
       ((division old start n d (j+1)).2*base+old (start+j))%d) := by
  have hn : n-j=(n-(j+1))+1 := by omega
  have shift : (fun k=>old (start+j+(k+1)))=(fun k=>old (start+(j+1)+k)) := by
    funext k
    congr 1
    omega
  simp only [division,hn,divideDigits,shift,Nat.add_zero]

theorem currentData_step (old : Nat → Nat) (start n d j : Nat) (hj : j < n) :
    Function.update (currentData old start n d (j+1)) (start+j)
      (((division old start n d (j+1)).2*base+old (start+j))/d)=currentData old start n d j := by
  funext i
  by_cases he : i=start+j
  · subst i
    simp [currentData,division_step old start n d j hj,prependDigit,show start+j < start+n by omega]
  · by_cases hi : start+(j+1) ≤ i ∧ i < start+n
    · have hi' : start+j ≤ i ∧ i < start+n := by omega
      have pos : i-(start+j)≠0 := by omega
      have sub : i-(start+j)-1=i-(start+(j+1)) := by omega
      simp only [Function.update_of_ne he,currentData,if_pos hi,if_pos hi',
        division_step old start n d j hj,prependDigit,if_neg pos,sub]
    · have hi' : ¬(start+j ≤ i ∧ i < start+n) := by omega
      simp [Function.update_of_ne he,currentData,hi,hi']

theorem division_remainder_lt (old : Nat → Nat) (start n d j : Nat) (hd : 0 < d) :
    (division old start n d j).2 < d :=
  divideDigits_remainder_lt base d (n-j) hd _

theorem currentData_slice (old : Nat → Nat) (start n d i : Nat) (hi : i < n) :
    currentData old start n d 0 (start+i)=(divideDigits base d (fun k=>old (start+k)) n).1 i := by
  simp [currentData,division,show start ≤ start+i ∧ start+i < start+n by omega]

theorem currentData_value (old : Nat → Nat) (start n d : Nat) :
    magnitude base n (fun i=>old (start+i))=
      d*magnitude base n (fun i=>currentData old start n d 0 (start+i))+(division old start n d 0).2 := by
  have eq : magnitude base n (fun i=>currentData old start n d 0 (start+i))=
      magnitude base n (divideDigits base d (fun k=>old (start+k)) n).1 := by
    apply Finset.sum_congr rfl
    intro i hi
    change currentData old start n d 0 (start+i)*base^i=_
    rw [currentData_slice old start n d i (Finset.mem_range.mp hi)]
  rw [eq]
  exact divideDigits_value base d n _

#print axioms division_step
#print axioms currentData_step
#print axioms currentData_value
end RH080Next.FFTPV.DivideSource
