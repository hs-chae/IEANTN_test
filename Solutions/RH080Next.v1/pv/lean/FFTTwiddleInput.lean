/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.TwiddleSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals

def objectAt (tableObject workObject : Nat) : MultiplyParameters.Var→Nat
  | .output | .a=>tableObject
  | .b | .work=>workObject

def startAt (j : Nat) : MultiplyParameters.Var→Nat
  | .output=>j*12
  | .a=>(j-1)*12
  | .b=>128
  | .work=>0

def extent (tableObject workObject n : Nat) (object : Nat) : Nat :=
  if object=workObject then 512 else n/2*12

def currentData (workObject : Nat) (tableData workData : Nat→Nat) (object : Nat) : Nat→Nat :=
  if object=workObject then workData else tableData

section ActualInputs
variable {F : Type} {state : State F} {tableObject workObject n owner j : Nat}
  {ids : TwiddleSource.Var→Nat} {tableData workData : Nat→Nat} {seed : FFT.IntegerModel.CInt}


def layout (h : View state tableObject workObject n ids owner j tableData workData seed) (inside : j<n/2) : ComplexSource.Layout where
  object:=objectAt tableObject workObject
  start:=startAt j
  length:=extent tableObject workObject n
  bound:=by
    intro r
    cases r <;> simp [objectAt,startAt,extent,h.different] <;> omega


theorem previous_small (h : View state tableObject workObject n ids owner j tableData workData seed) (inside : j<n/2) (c : Fin 2) : FFT.Limbs.magnitude 1000000000 5
    (fun d=>tableData ((j-1)*12+6*c.val+d))≤1000*10^36 := by
  have pairEq := h.tableValues (j-1) (by have a:=h.active;omega)
  have small := h.valuesSmall (j-1) (by omega)
  fin_cases c
  · have eq := congrArg Prod.fst pairEq
    simp only [ComplexSource.pair] at eq
    have absEq := congrArg Int.natAbs eq
    rw [ComplexSource.represented_natAbs] at absEq
    simpa using absEq.le.trans small.1
  · have eq := congrArg Prod.snd pairEq
    simp only [ComplexSource.pair] at eq
    have absEq := congrArg Int.natAbs eq
    rw [ComplexSource.represented_natAbs] at absEq
    simpa using absEq.le.trans small.2

theorem root_small (h : View state tableObject workObject n ids owner j tableData workData seed) (inside : j<n/2) (c : Fin 2) : FFT.Limbs.magnitude 1000000000 5
    (fun d=>workData (128+6*c.val+d))≤1000*10^36 := by
  fin_cases c
  · have eq := congrArg Prod.fst h.rootValue
    simp only [ComplexSource.pair] at eq
    have absEq := congrArg Int.natAbs eq
    rw [ComplexSource.represented_natAbs] at absEq
    simpa using absEq.le.trans h.rootSmall.1
  · have eq := congrArg Prod.snd h.rootValue
    simp only [ComplexSource.pair] at eq
    have absEq := congrArg Int.natAbs eq
    rw [ComplexSource.represented_natAbs] at absEq
    simpa using absEq.le.trans h.rootSmall.2

def input (h : View state tableObject workObject n ids owner j tableData workData seed) (inside : j<n/2) : ComplexSource.Input where
  layout:=layout h inside
  old:=currentData workObject tableData workData
  disjoint:=by
    intro r role
    cases r <;> simp_all [layout,objectAt,startAt,h.different]
  digits:=by
    intro r role c d hd
    cases r with
    | output=>simp at role
    | work=>simp at role
    | a=>simpa [layout,objectAt,startAt,currentData,h.different] using h.tableDigits (j-1) (by have a:=h.active;omega) c d hd
    | b=>simpa [layout,objectAt,startAt,currentData] using h.rootDigits c d hd
  signs:=by
    intro r role c
    cases r with
    | output=>simp at role
    | work=>simp at role
    | a=>simpa [layout,objectAt,startAt,currentData,h.different] using h.tableSigns (j-1) (by have a:=h.active;omega) c
    | b=>simpa [layout,objectAt,startAt,currentData] using h.rootSigns c
  magnitude:=by
    intro r role c
    cases r with
    | output=>simp at role
    | work=>simp at role
    | a=>simpa [layout,objectAt,startAt,currentData,h.different,ComplexSource.unit] using previous_small h inside c
    | b=>simpa [layout,objectAt,startAt,currentData,ComplexSource.unit] using root_small h inside c

theorem input_arrays (h : View state tableObject workObject n ids owner j tableData workData seed) (inside : j<n/2) : ∀r,WordArrayRep state ((input h inside).layout.object r)
    ((input h inside).layout.length ((input h inside).layout.object r))
    ((input h inside).old ((input h inside).layout.object r)) := by
  intro r
  cases r with
  | output=>simpa [input,layout,objectAt,extent,currentData,h.different] using h.table
  | a=>simpa [input,layout,objectAt,extent,currentData,h.different] using h.table
  | b=>simpa [input,layout,objectAt,extent,currentData] using h.work
  | work=>simpa [input,layout,objectAt,extent,currentData] using h.work

theorem input_arguments (h : View state tableObject workObject n ids owner j tableData workData seed) (inside : j<n/2) : ComplexSource.arguments (input h inside)=
    [.pointer (wordPointer tableObject (j*12)),.pointer (wordPointer tableObject ((j-1)*12)),
      .pointer (wordPointer workObject 128),.pointer (wordPointer workObject 0)] := by rfl

theorem computed_value (h : View state tableObject workObject n ids owner j tableData workData seed) (inside : j<n/2) : ComplexSource.resultPair (input h inside)=sequence seed j := by
  rw [ComplexSource.resultPair_eq_integer_mul]
  change FFT.IntegerModel.mul (ComplexSource.pair (currentData workObject tableData workData tableObject) ((j-1)*12))
    (ComplexSource.pair (currentData workObject tableData workData workObject) 128)=sequence seed j
  simp only [currentData,if_neg h.different,ite_true]
  rw [h.tableValues (j-1) (by have a:=h.active;omega),h.rootValue]
  have jj : j=(j-1)+1 := by have a:=h.active;omega
  conv_rhs=>rw [jj]
  rfl
end ActualInputs

#print axioms previous_small
#print axioms root_small
#print axioms input_arrays
#print axioms computed_value
end RH080Next.FFTPV.TwiddleSource
