/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexIntegerBridge
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace RH080Next.FFTPV.InputCell
open FFT.Limbs

def packed (base value : Nat) : Nat→Nat
  | 2=>value%base
  | 3=>(value/base)%base
  | 4=>value/base/base
  | _=>0

theorem packed_magnitude (base value : Nat) : magnitude base 5 (packed base value)=value*base^2:=by
  have expansion : value%base+base*((value/base)%base+base*(value/base/base))=value:=by
    rw [Nat.mod_add_div (value/base) base,Nat.mod_add_div value base]
  calc
    magnitude base 5 (packed base value)=
        (value%base+base*((value/base)%base+base*(value/base/base)))*base^2:=by
      simp [magnitude,Finset.sum_range_succ,packed]
      ring
    _=value*base^2:=congrArg (fun v=>v*base^2) expansion

def scale : Nat:=10000000000000000
def base : Nat:=1000000000

def magnitudeValue (encoded : Nat) : Nat:=if scale≤encoded then encoded-scale else scale-encoded
def signValue (encoded : Nat) : Nat:=if scale≤encoded then 0 else 1

def rawCell (encoded : Nat) : Nat→Nat:=
  Function.update (packed base (magnitudeValue encoded*100)) 5 (signValue encoded)

def cell (encoded : Nat) : Nat→Nat:=CanonicalSource.canonicalData (rawCell encoded) 0

theorem raw_magnitude (encoded : Nat) :
    magnitude base 5 (fun k=>rawCell encoded (0+k))=magnitudeValue encoded*100*base^2:=by
  have same : magnitude base 5 (fun k=>rawCell encoded (0+k))=
      magnitude base 5 (packed base (magnitudeValue encoded*100)):=by
    apply Finset.sum_congr rfl
    intro k hk
    have different : k≠5:=by have bound:=Finset.mem_range.mp hk;omega
    simp only [Nat.zero_add,rawCell,Function.update_of_ne different]
  exact same.trans (packed_magnitude base _)

theorem raw_sign (encoded : Nat) : rawCell encoded (0+5)=signValue encoded:=by simp [rawCell]

theorem represented_raw (encoded : Nat) :
    CanonicalSource.represented (rawCell encoded) 0=((encoded:Int)-(scale:Int))*100000000000000000000:=by
  have mag:=raw_magnitude encoded
  change signed (decide (rawCell encoded (0+5)≠0)) (magnitude base 5 (fun k=>rawCell encoded (0+k)))=_
  rw [raw_sign,mag]
  by_cases positive : scale≤encoded
  · simp only [signValue,magnitudeValue,positive,↓reduceIte,ne_eq,not_true_eq_false,decide_false,signed,Bool.false_eq_true,↓reduceIte]
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub positive]
    norm_num [base]
    ring
  · have order : encoded≤scale:=by omega
    simp only [signValue,magnitudeValue,positive,↓reduceIte,ne_eq,one_ne_zero,not_false_eq_true,decide_true,signed,↓reduceIte]
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub order]
    norm_num [base]
    ring

theorem represented_cell (encoded : Nat) :
    CanonicalSource.represented (cell encoded) 0=((encoded:Int)-(scale:Int))*100000000000000000000:=
  (CanonicalSource.canonicalData_preserves _ _).trans (represented_raw encoded)

#print axioms packed_magnitude
#print axioms represented_cell
end RH080Next.FFTPV.InputCell
