/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTMagnitudeIntoCall
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace RH080Next.FFTPV.MagnitudeIntoSource
open GoldbachDirect WordArrays

theorem finalData_digit (input : Input) (k : Nat) (hk : k<6) :
    finalData input (input.start+k)=if k=0 then input.value%base else if k=1 then input.value/base else 0:=by
  by_cases zero : k=0
  · subst k;simp [finalData]
  by_cases one : k=1
  · subst k;simp [finalData]
  simp only [finalData,Function.update_of_ne (show input.start+k≠input.start+1 by omega),
    Function.update_of_ne (show input.start+k≠input.start by omega),if_neg zero,if_neg one]
  exact ZeroSlice.zeroData_inside _ _ _ _ hk

theorem finalData_outside (input : Input) (k : Nat) (outside : k< input.start ∨ input.start+6≤k) :
    finalData input k=input.old k:=by
  unfold finalData
  rw [Function.update_of_ne (show k≠input.start+1 by omega),Function.update_of_ne (show k≠input.start by omega)]
  exact ZeroSlice.zeroData_outside _ _ _ _ outside

theorem finalData_normalized (input : Input) (k : Nat) (hk : k<6) : finalData input (input.start+k)<base:=by
  rw [finalData_digit input k hk]
  split_ifs
  · exact Nat.mod_lt _ (by norm_num [base])
  · exact (Nat.div_lt_iff_lt_mul (by norm_num [base])).mpr input.small
  · norm_num [base]

theorem finalData_magnitude (input : Input) : FFT.Limbs.magnitude base 5 (fun k=>finalData input (input.start+k))=input.value:=by
  unfold FFT.Limbs.magnitude
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  rw [finalData_digit input 0 (by omega),finalData_digit input 1 (by omega),finalData_digit input 2 (by omega),
    finalData_digit input 3 (by omega),finalData_digit input 4 (by omega)]
  norm_num only [ite_true,ite_false,pow_zero,pow_one,mul_one,zero_mul,add_zero,reduceCtorEq,reduceIte]
  simpa only [Nat.mul_comm] using Nat.mod_add_div input.value base

theorem finalData_sign (input : Input) : finalData input (input.start+5)=0:=by
  rw [finalData_digit input 5 (by omega)];rfl

#print axioms finalData_magnitude
#print axioms finalData_outside
end RH080Next.FFTPV.MagnitudeIntoSource
