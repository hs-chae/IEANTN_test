/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTConvertBoundSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DropTwoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

def base : Nat:=1000000000

def shifted (old : Nat→Nat) (start : Nat) : Nat→Nat→Nat
  | 0=>old
  | i+1=>Function.update (shifted old start i) (start+i) (old (start+i+2))

def dropped (old : Nat→Nat) (start : Nat) : Nat→Nat:=
  Function.update (Function.update (shifted old start 4) (start+4) 0) (start+5) 0

def lost (old : Nat→Nat) (start : Nat) : Nat:=old start+old (start+1)

theorem shifted_unread (old : Nat→Nat) (start i k : Nat) (outside : k<start ∨ start+i≤k) :
    shifted old start i k=old k:=by
  induction i with
  | zero=>rfl
  | succ i ih=>
    rw [shifted,Function.update_of_ne (by omega)]
    exact ih (by omega)

theorem shifted_processed (old : Nat→Nat) (start i k : Nat) (hk : k< i) :
    shifted old start i (start+k)=old (start+k+2):=by
  induction i with
  | zero=>omega
  | succ i ih=>
    by_cases eq : k=i
    · subst k;simp [shifted]
    · rw [shifted,Function.update_of_ne (by omega)]
      exact ih (by omega)

theorem dropped_outside (old : Nat→Nat) (start k : Nat) (outside : k<start ∨ start+6≤k) :
    dropped old start k=old k:=by
  unfold dropped
  rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
  exact shifted_unread old start 4 k (by omega)

theorem dropped_digits (old : Nat→Nat) (start k : Nat) (hk : k<6) :
    dropped old start (start+k)=if k<4 then old (start+k+2) else 0:=by
  unfold dropped
  by_cases h4 : k<4
  · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),shifted_processed old start 4 k h4]
    simp only [if_pos h4]
  · interval_cases k <;> simp [h4]

theorem low_two_bound {old : Nat→Nat} {start : Nat}
    (digits : ∀k,k<6 → old (start+k)<base) :
    FFT.Limbs.magnitude base 2 (fun k=>old (start+k))<base^2:=by
  have h0:=digits 0 (by norm_num)
  have h1:=digits 1 (by norm_num)
  simp only [Nat.add_zero] at h0
  simp [FFT.Limbs.magnitude,Finset.sum_range_succ,base] at *
  omega

theorem dropped_magnitude {old : Nat→Nat} {start : Nat}
    (digits : ∀k,k<6 → old (start+k)<base) :
    FFT.Limbs.magnitude base 6 (fun k=>dropped old start (start+k))=
      FFT.Limbs.magnitude base 6 (fun k=>old (start+k))/base^2:=by
  have split:=FFT.Limbs.magnitude_split base 2 4 (fun k=>old (start+k))
  have low:=low_two_bound digits
  have result : FFT.Limbs.magnitude base 6 (fun k=>dropped old start (start+k))=
      FFT.Limbs.magnitude base 4 (fun k=>old (start+(k+2))):=by
    have zero : dropped old start start=old (start+2):=by simpa using dropped_digits old start 0 (by norm_num)
    simp [FFT.Limbs.magnitude,Finset.sum_range_succ,dropped_digits,zero,show 0<6 by omega,
      show 1<6 by omega,show 2<6 by omega,show 3<6 by omega,show 4<6 by omega,show 5<6 by omega]
  rw [result]
  have shape : FFT.Limbs.magnitude base 6 (fun k=>old (start+k))=
      FFT.Limbs.magnitude base 2 (fun k=>old (start+k))+base^2*FFT.Limbs.magnitude base 4 (fun k=>old (start+(k+2))):=by
    simpa [Nat.add_comm] using split
  rw [shape,Nat.add_mul_div_left _ _ (by norm_num [base]),Nat.div_eq_of_lt low,Nat.zero_add]

theorem lost_zero_iff_remainder {old : Nat→Nat} {start : Nat}
    (digits : ∀k,k<6 → old (start+k)<base) :
    lost old start=0 ↔ FFT.Limbs.magnitude base 6 (fun k=>old (start+k))%base^2=0:=by
  have split:=FFT.Limbs.magnitude_split base 2 4 (fun k=>old (start+k))
  have low:=low_two_bound digits
  change lost old start=0 ↔ _
  rw [split,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt low]
  simp [lost,FFT.Limbs.magnitude,Finset.sum_range_succ,base]

#print axioms dropped_magnitude
#print axioms lost_zero_iff_remainder
end RH080Next.FFTPV.DropTwoSource
