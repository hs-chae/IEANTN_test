/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootIterationMath
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect WordArrays

inductive Region where | x | x2 | ct | st | cr | sr deriving DecidableEq

def regionStart (input : Input) : Region → Nat
  | .x=>input.layout.workStart | .x2=>input.layout.workStart+6
  | .ct=>input.layout.workStart+12 | .st=>input.layout.workStart+18
  | .cr=>input.layout.rootStart | .sr=>input.layout.rootStart+6

def regionValue (n j : Nat) : Region → Int
  | .x=>xInteger n | .x2=>x2Integer n
  | .ct=>(taylorState n j).ct | .st=>(taylorState n j).st
  | .cr=>(taylorState n j).cr | .sr=>(taylorState n j).sr

def Tracked (input : Input) (data : Nat → Nat) (values : Region → Int) : Prop:=
  ∀r,FixedValue data (regionStart input r) (values r)

theorem TaylorValues.tracked {input : Input} {data : Nat → Nat} {j : Nat}
    (h : TaylorValues input data j) : Tracked input data (regionValue input.n j):=by
  intro r;cases r
  · exact h.x
  · exact h.x2
  · exact h.ct
  · exact h.st
  · exact h.cr
  · exact h.sr

theorem Tracked.taylorValues {input : Input} {data : Nat → Nat} {j : Nat}
    (h : Tracked input data (regionValue input.n j)) : TaylorValues input data j:=
  ⟨h .x,h .x2,h .ct,h .st,h .cr,h .sr⟩

theorem region_bound (input : Input) (r : Region) : regionStart input r+6≤ input.layout.size:=by
  have w:=input.layout.workBound;have p:=input.layout.rootBound
  cases r <;> simp only [regionStart] <;> omega

theorem regions_disjoint (input : Input) (a b : Region) (different : a≠b) :
    regionStart input a+6≤ regionStart input b ∨ regionStart input b+6≤ regionStart input a := by
  have separate:=input.layout.separate
  cases a <;> cases b <;> simp only [regionStart] at * <;> first | contradiction | omega

theorem region_outside_temp (input : Input) (r : Region) (k : Nat) (hk : k<6) :
    (regionStart input r+k< input.layout.workStart+24 ∨ input.layout.workStart+30≤ regionStart input r+k) ∧
    (regionStart input r+k< input.layout.workStart+36 ∨ input.layout.workStart+46≤ regionStart input r+k) := by
  have separate:=input.layout.separate
  cases r <;> simp only [regionStart] <;> omega

theorem Tracked.congr {input : Input} {old data : Nat → Nat} {values : Region → Int}
    (h : Tracked input old values) (same : ∀r k,k<6 → data (regionStart input r+k)=old (regionStart input r+k)) :
    Tracked input data values:=fun r=>(h r).congr (same r)

theorem Tracked.update {input : Input} {old data : Nat → Nat} {values : Region → Int}
    (h : Tracked input old values) (r : Region) (value : Int) (target : FixedValue data (regionStart input r) value)
    (outside : ∀k,(k< regionStart input r ∨ regionStart input r+6≤ k) → data k=old k) :
    Tracked input data (Function.update values r value) := by
  intro q
  by_cases same : q=r
  · subst q;simpa only [Function.update_self] using target
  · rw [Function.update_of_ne same]
    apply (h q).congr
    intro k hk
    apply outside
    have separate:=regions_disjoint input q r same
    omega

theorem Tracked.after_temporary_multiply {input : Input} {old data : Nat → Nat} {values : Region → Int}
    (h : Tracked input old values)
    (outside : ∀k,k< input.layout.size → (k< input.layout.workStart+24 ∨ input.layout.workStart+30≤ k) →
      (k< input.layout.workStart+36 ∨ input.layout.workStart+46≤ k) → data k=old k) :
    Tracked input data values := by
  apply h.congr
  intro r k hk
  have bounds:=region_bound input r
  have out:=region_outside_temp input r k hk
  exact outside _ (by omega) out.1 out.2

theorem fixed_copy_value {old : Nat → Nat} {source target : Nat} {value : Int}
    (h : FixedValue old source value) :
    FixedValue (CopyLoop.prefixData old (fun i=>old (source+i)) target 6) target value := by
  apply h.congr
  intro k hk
  simp [CopyLoop.prefixData,show target≤ target+k ∧ target+k< target+6 by omega]

theorem copy_outside (old : Nat → Nat) (source target k : Nat)
    (outside : k< target ∨ target+6≤ k) :
    CopyLoop.prefixData old (fun i=>old (source+i)) target 6 k=old k := by
  simp [CopyLoop.prefixData,show ¬(target≤ k ∧ k< target+6) by omega]

#print axioms regions_disjoint
#print axioms Tracked.update
#print axioms Tracked.after_temporary_multiply
#print axioms fixed_copy_value
end RH080Next.FFTPV.RootSource
