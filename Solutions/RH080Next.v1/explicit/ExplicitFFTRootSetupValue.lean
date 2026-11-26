/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootValue
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect WordArrays FFT.Limbs
open IncrementSource (base)

theorem work_outside_root (input : Input) (k : Nat) (hk : k<80) :
    ¬(input.layout.rootStart≤ input.layout.workStart+k ∧ input.layout.workStart+k< input.layout.rootStart+12) := by
  rcases input.layout.separate with lo|hi <;> omega

theorem setupData_work_low (input : Input) (data : Nat → Nat) (k : Nat) (hk : k<18) :
    setupData input data (input.layout.workStart+k)=(if k=16 then 1 else data (input.layout.workStart+k)) := by
  have rootOutside:=work_outside_root input k (by omega)
  have rootCopyOutside : ¬(input.layout.rootStart+6≤ input.layout.workStart+k ∧
      input.layout.workStart+k< input.layout.rootStart+6+6):=by omega
  have workCopyOutside : ¬(input.layout.workStart+18≤ input.layout.workStart+k ∧
      input.layout.workStart+k< input.layout.workStart+18+6):=by omega
  have rootDifferent : input.layout.workStart+k≠input.layout.rootStart+4:=by omega
  have k18 : ¬18≤k:=by omega
  simp [setupData,CopyLoop.prefixData,rootCopyOutside,workCopyOutside,k18,Function.update_apply,rootDifferent,
    ZeroSlice.zeroData,CopyLoop.prefixData,rootOutside]

theorem setupData_root_lower (input : Input) (data : Nat → Nat) (k : Nat) (hk : k<6) :
    setupData input data (input.layout.rootStart+k)=(if k=4 then 1 else 0) := by
  have separate:=input.layout.separate
  have rootCopyOutside : ¬(input.layout.rootStart+6≤ input.layout.rootStart+k ∧
      input.layout.rootStart+k< input.layout.rootStart+6+6):=by omega
  have workCopyOutside : ¬(input.layout.workStart+18≤ input.layout.rootStart+k ∧
      input.layout.rootStart+k< input.layout.workStart+18+6):=by rcases separate with lo|hi <;> omega
  have workDifferent : input.layout.rootStart+k≠input.layout.workStart+16:=by rcases separate with lo|hi <;> omega
  have cleared : input.layout.rootStart≤ input.layout.rootStart+k ∧ input.layout.rootStart+k< input.layout.rootStart+12:=by omega
  have k6 : ¬6≤k:=by omega
  simp [setupData,CopyLoop.prefixData,rootCopyOutside,workCopyOutside,k6,Function.update_apply,workDifferent,
    ZeroSlice.zeroData,CopyLoop.prefixData,cleared]

theorem setupData_work_sine (input : Input) (data : Nat → Nat) (k : Nat) (hk : k<6) :
    setupData input data (input.layout.workStart+18+k)=data (input.layout.workStart+k) := by
  have rootOutside:=work_outside_root input (18+k) (by omega)
  have rootSourceOutside:=work_outside_root input k (by omega)
  have rootCopyOutside : ¬(input.layout.rootStart+6≤ input.layout.workStart+18+k ∧
      input.layout.workStart+18+k< input.layout.rootStart+6+6):=by omega
  have workCopyInside : input.layout.workStart+18≤ input.layout.workStart+18+k ∧
      input.layout.workStart+18+k< input.layout.workStart+18+6:=by omega
  have rootDifferent : input.layout.workStart+k≠input.layout.rootStart+4:=by omega
  have workDifferent : input.layout.workStart+k≠input.layout.workStart+16:=by omega
  have k16 : k≠16:=by omega
  simp [setupData,CopyLoop.prefixData,rootCopyOutside,workCopyInside,k16,Function.update_apply,
    rootDifferent,workDifferent,ZeroSlice.zeroData,CopyLoop.prefixData,rootSourceOutside]

theorem setupData_root_sine (input : Input) (data : Nat → Nat) (k : Nat) (hk : k<6) :
    setupData input data (input.layout.rootStart+6+k)=data (input.layout.workStart+k) := by
  have rootSourceOutside:=work_outside_root input k (by omega)
  have rootCopyInside : input.layout.rootStart+6≤ input.layout.rootStart+6+k ∧
      input.layout.rootStart+6+k< input.layout.rootStart+6+6:=by omega
  have workCopyOutside : ¬(input.layout.workStart+18≤ input.layout.workStart+k ∧
      input.layout.workStart+k< input.layout.workStart+18+6):=by omega
  have rootDifferent : input.layout.workStart+k≠input.layout.rootStart+4:=by omega
  have workDifferent : input.layout.workStart+k≠input.layout.workStart+16:=by omega
  have k16 : k≠16:=by omega
  have k18 : ¬18≤k:=by omega
  simp [setupData,CopyLoop.prefixData,rootCopyInside,workCopyOutside,k16,k18,Function.update_apply,
    rootDifferent,workDifferent,ZeroSlice.zeroData,CopyLoop.prefixData,rootSourceOutside]

/-- Actual named values required at entry to the ten original source
iterations. Each value is interpreted from the current real memory words. -/
structure TaylorValues (input : Input) (data : Nat → Nat) (j : Nat) : Prop where
  x : FixedValue data input.layout.workStart (xInteger input.n)
  x2 : FixedValue data (input.layout.workStart+6) (x2Integer input.n)
  ct : FixedValue data (input.layout.workStart+12) (taylorState input.n j).ct
  st : FixedValue data (input.layout.workStart+18) (taylorState input.n j).st
  cr : FixedValue data input.layout.rootStart (taylorState input.n j).cr
  sr : FixedValue data (input.layout.rootStart+6) (taylorState input.n j).sr

theorem setup_values (input : Input) (data : Nat → Nat)
    (x : FixedValue data input.layout.workStart (xInteger input.n))
    (x2 : FixedValue data (input.layout.workStart+6) (x2Integer input.n))
    (zeroCt : ∀k < 6,data (input.layout.workStart+12+k)=0) :
    TaylorValues input (setupData input data) 0 := by
  have cr:=fixed_unit (setupData input data) input.layout.rootStart (setupData_root_lower input data)
  have ct : FixedValue (setupData input data) (input.layout.workStart+12) FFT.IntegerModel.unit:=by
    apply fixed_unit
    intro k hk
    have low:=setupData_work_low input data (12+k) (by omega)
    have original : data (input.layout.workStart+(12+k))=0:=by simpa only [Nat.add_assoc] using zeroCt k hk
    have same : (12+k=16) ↔ k=4:=by omega
    simpa only [Nat.add_assoc,original,same] using low
  refine ⟨?_,?_,ct,?_,cr,?_⟩
  · apply x.congr
    intro k hk
    rw [setupData_work_low input data k (by omega),if_neg (by omega)]
  · apply x2.congr
    intro k hk
    have low:=setupData_work_low input data (6+k) (by omega)
    simpa only [Nat.add_assoc,if_neg (show ¬6+k=16 by omega)] using low
  · apply x.congr
    intro k hk
    simpa only [Nat.add_assoc] using setupData_work_sine input data k hk
  · apply x.congr
    intro k hk
    simpa only [Nat.add_assoc] using setupData_root_sine input data k hk

#print axioms setupData_work_low
#print axioms setupData_root_sine
#print axioms setup_values
end RH080Next.FFTPV.RootSource
