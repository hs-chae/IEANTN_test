/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootFrames
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)

def termStatements (offset : Nat) (divisor : Expr) : List Stmt:=[
  multiplyStatement .work 24 .work offset .work 6,
  copySliceStatement .work offset .work 24,floorDivideStatement .work offset divisor]

/-- The actual three source instructions computing one next Taylor term:
fixed multiplication into the temporary slice, copy back, then floor division.
All six mathematical regions survive the scratch mutation; only the selected
term region changes after the copy and division. -/
theorem term_execution {F : Type} (context : Context F) (functions : Functions context)
    {before : State F} {input : Input} {owner statusId indexId index : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data index)
    (values : Region → Int) (tracked : Tracked input data values)
    (r : Region) (offset : Nat) (offsetBound : offset≤18) (region : regionStart input r=input.layout.workStart+offset)
    (divisor : Expr) (d : Nat) (positive : 0< d) (small : d< base)
    (divisorPure : SourcePure.CallFree divisor)
    (readDivisor : ∀{state : State F} {current : Nat → Nat},
      Runtime state input owner statusId indexId ids current index → Eval context state divisor (.integer (integer64 d)) state)
    (termSmall : (values r).natAbs≤1000*10^36) (x2Small : (values .x2).natAbs≤1000*10^36)
    (productNonnegative : 0≤(values r*values .x2)/FFT.IntegerModel.unit) :
    ∃after nextData,ExecList context before (termStatements offset divisor) .normal after ∧
      EveryList context before (termStatements offset divisor) .normal after ∧
      Runtime after input owner statusId indexId ids nextData index ∧
      Tracked input nextData (Function.update values r (((values r*values .x2)/FFT.IntegerModel.unit)/(d:Int))) ∧ IncrementSource.FullCallerFrame before after input.layout.object ∧
      ∀k,k < input.layout.size → (k < input.layout.workStart ∨ input.layout.workStart+80≤ k) → nextData k=data k := by
  have workBound:=input.layout.workBound
  have termRep : FixedValue data (pointerStart input .work+offset) (values r):=by
    simpa only [pointerStart,region] using tracked r
  have x2Rep : FixedValue data (pointerStart input .work+6) (values .x2):=tracked .x2
  obtain ⟨s1,data1,run1,every1,view1,temp,frame1,outside1⟩:=multiply_execution context functions.multiply functions.zero
    functions.increment functions.canonical h.view h.active .work (Or.inr rfl) 24 .work (Or.inr rfl) offset
    .work (Or.inr rfl) 6 (values r) (values .x2) termRep x2Rep termSmall x2Small
    (by simp only [pointerStart];omega) (by simp only [pointerStart];omega) (by simp only [pointerStart];omega)
    (Or.inl (by simp only [pointerStart];omega)) (Or.inl (by simp only [pointerStart];omega))
    (Or.inl (by simp only [pointerStart];omega)) (by norm_num) (by omega) (by norm_num)
  have rt1:=h.after_multiply view1 frame1
  have tracked1 : Tracked input data1 values:=by
    apply tracked.after_temporary_multiply
    intro k hk ho hs
    exact outside1 k hk ho hs
  obtain ⟨s2,run2,every2,rt2,frame2,birth2⟩:=runtime_copy_execution context functions.copy rt1 .work (Or.inr rfl) offset .work (Or.inr rfl) 24
    (by simp only [pointerStart];omega) (by simp only [pointerStart];omega)
    (Or.inr (Or.inl (by simp only [pointerStart];omega))) (by omega) (by norm_num)
  let data2:=CopyLoop.prefixData data1 (fun i=>data1 (input.layout.workStart+24+i)) (input.layout.workStart+offset) 6
  have copied : FixedValue data2 (regionStart input r) ((values r*values .x2)/FFT.IntegerModel.unit):=by
    rw [region]
    exact fixed_copy_value temp
  have tracked2 : Tracked input data2 (Function.update values r ((values r*values .x2)/FFT.IntegerModel.unit)):=by
    apply tracked1.update r _ copied
    intro k outside
    apply copy_outside
    simpa only [region] using outside
  obtain ⟨after,run3,every3,view3,divided,frame3⟩:=floor_divide_execution context functions.divide functions.increment rt2.view rt2.active
    .work (Or.inr rfl) offset d divisor (readDivisor rt2) divisorPure ((values r*values .x2)/FFT.IntegerModel.unit)
    (by simpa only [pointerStart,region] using copied) productNonnegative positive small
    (by simp only [pointerStart];omega) (by omega)
  have rt3:=rt2.after_unary view3 frame3
  have finalValue : FixedValue (DivideSource.roundedData data2 (input.layout.workStart+offset) 5 d 0)
      (regionStart input r) (((values r*values .x2)/FFT.IntegerModel.unit)/(d:Int)):=by
    simpa only [pointerStart,region] using divided
  have tracked3:=tracked2.update r _ finalValue (by
    intro k outside
    apply DivideSource.roundedData_outside
    rw [region] at outside
    omega)
  have updateValues : Function.update (Function.update values r ((values r*values .x2)/FFT.IntegerModel.unit)) r
      (((values r*values .x2)/FFT.IntegerModel.unit)/(d:Int))=
      Function.update values r (((values r*values .x2)/FFT.IntegerModel.unit)/(d:Int)):=by
    exact Function.update_idem _ _ _
  rw [updateValues] at tracked3
  have combined : ApplicationBirthFrame.Frame before.nextObject before after [input.layout.object]:=
    ((multiply_frame frame1).trans (lower_frame birth2 frame1.frame.nextObject)).trans
      (lower_frame (unary_frame frame3) (frame1.frame.nextObject.trans birth2.nextObject))
  have frame:=full_caller_frame (frame3.environment.trans (frame2.environment.trans frame1.environment))
    (frame3.scope.trans (frame2.scope.trans frame1.scope)) combined
  refine ⟨after,_,.cons run1 (.cons run2 (.cons run3 .nil)),
    every_cons every1 (every_cons every2 (every_cons every3 (every_nil after))),rt3,tracked3,frame,?_⟩
  intro k hk outsideWork
  have divOutside : ¬(input.layout.workStart+offset≤ k ∧ k< input.layout.workStart+offset+5):=by
    rcases outsideWork with lo|hi <;> omega
  have copyOutside : k< input.layout.workStart+offset ∨ input.layout.workStart+offset+6≤ k:=by
    rcases outsideWork with lo|hi <;> omega
  have unchanged1:=outside1 k hk
    (by simp only [pointerStart];rcases outsideWork with lo|hi <;> omega)
    (by rcases outsideWork with lo|hi <;> omega)
  have unchanged2 : data2 k=data1 k:=copy_outside _ _ _ _ copyOutside
  exact (DivideSource.roundedData_outside _ _ _ _ _ _ divOutside).trans (unchanged2.trans unchanged1)

#print axioms term_execution
end RH080Next.FFTPV.RootSource
