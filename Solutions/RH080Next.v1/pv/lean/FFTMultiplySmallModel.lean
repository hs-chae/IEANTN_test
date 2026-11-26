/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTLimbMultiplication
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySmallSource
open FFT.Limbs

def base : Nat:=1000000000

def scaledRow (old : Nat→Nat) (start factor j : Nat) : (Nat→Nat)×Nat:=
  row base 0 factor (fun k=>old (start+k)) (fun _=>0) j

theorem row_unread (old : Nat→Nat) (start factor j : Nat) : (scaledRow old start factor j).1 j=0:=
  row_untouched base 0 factor (fun k=>old (start+k)) (fun _=>0) j j (Or.inr (by omega))

theorem row_step (old : Nat→Nat) (start factor j : Nat) :
    scaledRow old start factor (j+1)=
      (Function.update (scaledRow old start factor j).1 j
        ((old (start+j)*factor+(scaledRow old start factor j).2)%base),
        (old (start+j)*factor+(scaledRow old start factor j).2)/base) := by
  change (Function.update (scaledRow old start factor j).1 (0+j)
      (((scaledRow old start factor j).1 (0+j)+factor*old (start+j)+(scaledRow old start factor j).2)%base),
      ((scaledRow old start factor j).1 (0+j)+factor*old (start+j)+(scaledRow old start factor j).2)/base)=_
  rw [Nat.zero_add,row_unread]
  simp only [zero_add,Nat.mul_comm]

theorem row_carry_bound (old : Nat→Nat) (start factor j : Nat) (positive : 0<factor)
    (digits : ∀k,k<j → old (start+k)<base) : (scaledRow old start factor j).2<factor := by
  induction j with
  | zero=>exact positive
  | succ j ih=>
    have carryBound:=ih (fun k hk=>digits k (by omega))
    have digitBound:=digits j (by omega)
    have productBound : old (start+j)*factor+(scaledRow old start factor j).2<base*factor:=by
      have hmul:=Nat.mul_le_mul_right factor (show old (start+j)+1≤base by omega)
      nlinarith
    rw [row_step]
    exact (Nat.div_lt_iff_lt_mul (by norm_num [base])).mpr (by simpa only [Nat.mul_comm] using productBound)

/-- Non-strict carry invariant includes the actual quadrature factor0 call. -/
theorem row_carry_le (old : Nat→Nat) (start factor j : Nat)
    (digits : ∀k,k<j → old (start+k)<base) : (scaledRow old start factor j).2≤factor:=by
  induction j with
  | zero=>exact Nat.zero_le factor
  | succ j ih=>
    have carryBound:=ih (fun k hk=>digits k (by omega))
    have digitBound:=digits j (by omega)
    have productBound : old (start+j)*factor+(scaledRow old start factor j).2≤base*factor:=by
      have hmul:=Nat.mul_le_mul_right factor (show old (start+j)+1≤base by omega)
      nlinarith
    rw [row_step]
    have quotient : (old (start+j)*factor+(scaledRow old start factor j).2)/base≤(base*factor)/base:=
      Nat.div_le_div_right productBound
    exact quotient.trans_eq (Nat.mul_div_cancel_left factor (by norm_num [base]))

def currentData (old : Nat→Nat) (start factor j index : Nat) : Nat:=
  if start≤ index ∧ index<start+j then (scaledRow old start factor j).1 (index-start) else old index

theorem currentData_zero (old : Nat→Nat) (start factor : Nat) : currentData old start factor 0=old:=by
  funext i;simp [currentData]

theorem currentData_unread (old : Nat→Nat) (start factor j : Nat) :
    currentData old start factor j (start+j)=old (start+j):=by simp [currentData]

theorem currentData_step (old : Nat→Nat) (start factor j : Nat) :
    Function.update (currentData old start factor j) (start+j)
      ((old (start+j)*factor+(scaledRow old start factor j).2)%base)=currentData old start factor (j+1) := by
  funext i
  by_cases same : i=start+j
  · subst i;simp [currentData,row_step]
  · by_cases inside : start≤ i ∧ i<start+j
    · have different : i-start≠j:=by omega
      simp [currentData,Function.update_of_ne same,inside,
        show start≤ i ∧ i<start+(j+1) by omega,row_step,Function.update_of_ne different]
    · simp [currentData,Function.update_of_ne same,inside,
        show ¬(start≤ i ∧ i<start+(j+1)) by omega]

/-- Exact positional value conservation of source in-place multiplication,
reusing the full schoolbook row proof rather than an output certificate. -/
theorem final_value (old : Nat→Nat) (start factor n : Nat) :
    value base n (fun k=>currentData old start factor n (start+k))+
      ((scaledRow old start factor n).2:Int)*(base:Int)^n=
        (factor:Int)*value base n (fun k=>old (start+k)) := by
  have math:=row_value base 0 factor (fun k=>old (start+k)) (fun _=>0) n n (by omega)
  have input : (fun k=>currentData old start factor n (start+k))=
      fun k=>if k<n then (scaledRow old start factor n).1 k else old (start+k) := by
    funext k;simp [currentData]
  have values : value base n (fun k=>currentData old start factor n (start+k))=
      value base n (scaledRow old start factor n).1 := by
    unfold value
    apply Finset.sum_congr rfl
    intro k hk
    have below:=Finset.mem_range.mp hk
    simp [currentData,show start≤start+k ∧ start+k<start+n by omega]
  rw [values]
  simpa [scaledRow,value] using math

#print axioms row_step
#print axioms row_carry_bound
#print axioms currentData_step
#print axioms final_value
end RH080Next.FFTPV.MultiplySmallSource
