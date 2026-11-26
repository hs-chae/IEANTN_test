/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootSetup
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect WordArrays FFT.Limbs
open IncrementSource (base)

/-- Mathematical interpretation of one actual six-word fixed-point number. -/
structure FixedValue (data : Nat → Nat) (start : Nat) (value : Int) : Prop where
  digits : ∀k < 5,data (start+k)< base
  sign : data (start+5)≤1
  represented : CanonicalSource.represented data start=value

theorem FixedValue.congr {a b : Nat → Nat} {sa sb : Nat} {value : Int}
    (h : FixedValue a sa value) (same : ∀k < 6,b (sb+k)=a (sa+k)) : FixedValue b sb value := by
  have magnitude : magnitude 1000000000 5 (fun k=>b (sb+k))=magnitude 1000000000 5 (fun k=>a (sa+k)):=by
    apply Finset.sum_congr rfl
    intro k hk
    change b (sb+k)*_=a (sa+k)*_
    rw [same k (by have hk:=Finset.mem_range.mp hk;omega)]
  exact ⟨fun k hk=>by rw [same k (by omega)];exact h.digits k hk,
    by rw [same 5 (by omega)];exact h.sign,
    by unfold CanonicalSource.represented;rw [magnitude,same 5 (by omega)];exact h.represented⟩

private theorem signed_natAbs (negative : Bool) (m : Nat) : (signed negative m).natAbs=m:=by
  cases negative <;> simp [signed]

theorem represented_natAbs (data : Nat → Nat) (start : Nat) :
    (CanonicalSource.represented data start).natAbs=magnitude base 5 (fun k=>data (start+k)) :=
  signed_natAbs _ _

theorem FixedValue.small {data : Nat → Nat} {start : Nat} {value : Int}
    (h : FixedValue data start value) (bound : value.natAbs≤1000*10^36) :
    magnitude base 5 (fun k=>data (start+k))≤1000*10^36:=by
  rw [←represented_natAbs,h.represented];exact bound

theorem xData_fixed (input : Input) : FixedValue (xData input) input.layout.workStart (xInteger input.n):=
  ⟨xData_digits input,by rw [xData_zero_work input 5 (by omega) (by omega)];omega,xData_integer input⟩

theorem fixed_unit (data : Nat → Nat) (start : Nat)
    (words : ∀k < 6,data (start+k)=if k=4 then 1 else 0) : FixedValue data start FFT.IntegerModel.unit := by
  have values : ∀k < 5,data (start+k)< base:=by
    intro k hk;rw [words k (by omega)];split_ifs <;> norm_num [base]
  refine ⟨values,?_,?_⟩
  · rw [words 5 (by omega)];norm_num
  · unfold CanonicalSource.represented magnitude signed
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    rw [words 0 (by omega),words 1 (by omega),words 2 (by omega),words 3 (by omega),words 4 (by omega),words 5 (by omega)]
    norm_num [FFT.IntegerModel.unit]

#print axioms FixedValue.congr
#print axioms represented_natAbs
#print axioms fixed_unit
end RH080Next.FFTPV.RootSource
