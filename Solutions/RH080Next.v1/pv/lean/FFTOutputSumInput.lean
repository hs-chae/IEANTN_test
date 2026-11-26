/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTOutputSumBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.OutputSumSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

def extent (workObject n object : Nat) : Nat:=if object=workObject then 512 else n*12
def dataAt (workObject : Nat) (outputData workData : Nat→Nat) (object : Nat) : Nat→Nat:=
  if object=workObject then workData else outputData

/-- Opaque-input conservation avoids reducing six concrete update trees during
application type conversion; it is the proved actual source arithmetic model. -/
theorem conserved_total (input : AddMagnitudeSource.Input) (sum sample : Nat)
    (zero : (AddMagnitudeSource.row input input.layout.n).2=0)
    (oldValue : FFT.Limbs.magnitude AddMagnitudeSource.base input.layout.n
      (fun d=>input.old input.layout.outObject (input.layout.outStart+d))=sum)
    (newValue : FFT.Limbs.magnitude AddMagnitudeSource.base input.layout.n
      (AddMagnitudeSource.aDigit input)=sample) :
    FFT.Limbs.magnitude AddMagnitudeSource.base input.layout.n
      (fun d=>AddMagnitudeSource.currentData input input.layout.n (input.layout.outStart+d))=sum+sample := by
  have conservation:=AddMagnitudeSource.result_conservation input
  rw [zero,Nat.zero_mul,Nat.add_zero,oldValue,newValue] at conservation
  exact conservation

section Inputs
variable {F : Type} {state : State F} {outputObject workObject n owner i : Nat}
  {ids : Var→Nat} {outputData workData : Nat→Nat} {samples : Nat→FFT.IntegerModel.CInt}

def input (h : View state outputObject workObject n ids owner i outputData workData samples) (inside : i<n) : AddMagnitudeSource.Input where
  layout:={
    outObject:=workObject
    aObject:=outputObject
    length:=extent workObject n
    outStart:=192
    aStart:=i*12
    n:=6
    outBound:=by simp [extent]
    aBound:=by simp [extent,h.different];omega
    safe:=Or.inl h.different.symm
    small:=by omega
  }
  old:=dataAt workObject outputData workData
  outDigits:=by simpa [dataAt,AddMagnitudeSource.base] using h.totalDigits
  aDigits:=by simpa [dataAt,h.different,AddMagnitudeSource.base] using h.outputDigits i inside


theorem input_arrays (h : View state outputObject workObject n ids owner i outputData workData samples) (inside : i<n) :
    WordArrayRep state (input h inside).layout.outObject ((input h inside).layout.length (input h inside).layout.outObject)
      ((input h inside).old (input h inside).layout.outObject) ∧
    WordArrayRep state (input h inside).layout.aObject ((input h inside).layout.length (input h inside).layout.aObject)
      ((input h inside).old (input h inside).layout.aObject) := by
  exact ⟨by simpa [input,extent,dataAt] using h.work,by simpa [input,extent,dataAt,h.different] using h.output⟩

theorem input_magnitude (h : View state outputObject workObject n ids owner i outputData workData samples) (inside : i<n) :
    FFT.Limbs.magnitude AddMagnitudeSource.base (input h inside).layout.n (AddMagnitudeSource.aDigit (input h inside))=(samples i).1.natAbs := by
  have eq := h.outputValues i inside
  have absEq := congrArg Int.natAbs eq
  change (CanonicalSource.represented outputData (i*12)).natAbs=(samples i).1.natAbs at absEq
  rw [ComplexSource.represented_natAbs] at absEq
  rw [←absEq]
  simp [input,dataAt,h.different,AddMagnitudeSource.base,FFT.Limbs.magnitude,
    Finset.sum_range_succ,AddMagnitudeSource.aDigit]

theorem input_status_zero (h : View state outputObject workObject n ids owner i outputData workData samples) (inside : i<n) :
    (AddMagnitudeSource.row (input h inside) 6).2=0 := by
  apply AddMagnitudeSource.zero_status_of_small
  have value : FFT.Limbs.magnitude 1000000000 6 (fun d=>workData (192+d))=partialSum samples i:=by simpa using h.totalValue
  have bound:=partialSum_le (Nat.le_of_lt inside) h.outputSmall
  have sample:=h.outputSmall i inside
  have nb:=h.nbound
  have im:=input_magnitude h inside
  change FFT.Limbs.magnitude AddMagnitudeSource.base 6 (AddMagnitudeSource.aDigit (input h inside))=(samples i).1.natAbs at im
  change FFT.Limbs.magnitude AddMagnitudeSource.base 6 (fun j=>(input h inside).old workObject (192+j))+
    FFT.Limbs.magnitude AddMagnitudeSource.base 6 (AddMagnitudeSource.aDigit (input h inside))<AddMagnitudeSource.base^6
  rw [show FFT.Limbs.magnitude AddMagnitudeSource.base 6 (fun j=>(input h inside).old workObject (192+j))=partialSum samples i by simpa [input,dataAt,AddMagnitudeSource.base] using value,im]
  norm_num [AddMagnitudeSource.base]
  omega
end Inputs

#print axioms input_arrays
#print axioms input_magnitude
#print axioms input_status_zero
end RH080Next.FFTPV.OutputSumSource
