/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.Machine

namespace ScopedC.StateWordEquality
open ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

theorem split_and {a b : Bool} (h : (a && b) = true) : a=true ∧ b=true := by
  cases a <;> cases b <;> simp_all

def listEq {α : Type} (test : α → α → Bool) : List α → List α → Bool
  | [],[] => true
  | a::as,b::bs => test a b && listEq test as bs
  | _,_ => false

theorem listEq_sound {α : Type} {test : α → α → Bool}
    (sound : ∀ a b, test a b = true → a=b) {as bs : List α}
    (h : listEq test as bs = true) : as=bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [listEq]
  | cons a as ih =>
      cases bs with
      | nil => simp [listEq] at h
      | cons b bs =>
          obtain ⟨ha,hs⟩ := split_and h
          rw [sound a b ha,ih hs]

/-- Bounded structural equality. Fuel exhaustion rejects rather than accepting
unexamined nested values. This does not execute or certify a mathematical
program; source execution is proved separately with SourceCallExecute. -/
def valueEq : Nat → Value → Value → Bool
  | 0,_,_ => false
  | fuel+1,.integer a,.integer b => decide (a=b)
  | fuel+1,.natObject a,.natObject b => decide (a=b)
  | fuel+1,.record tag as,.record other bs => decide (tag=other) && listEq (valueEq fuel) as bs
  | fuel+1,.aggregate as,.aggregate bs => listEq (valueEq fuel) as bs
  | fuel+1,.pointer a wa,.pointer b wb => decide (a=b ∧ wa=wb)
  | fuel+1,.null,.null => true
  | fuel+1,.uninitialized,.uninitialized => true
  | fuel+1,.unit,.unit => true
  | _,_,_ => false

theorem valueEq_sound (fuel : Nat) {a b : Value} (h : valueEq fuel a b = true) : a=b := by
  induction fuel generalizing a b with
  | zero => simp [valueEq] at h
  | succ fuel ih =>
      cases a <;> cases b <;> simp only [valueEq,Bool.false_eq_true] at h
      all_goals try contradiction
      all_goals try rfl
      case integer.integer a b => exact congrArg Value.integer (of_decide_eq_true h)
      case natObject.natObject a b => exact congrArg Value.natObject (of_decide_eq_true h)
      case record.record tag as other bs =>
        obtain ⟨hn,hs⟩ := split_and h
        have names : tag=other := of_decide_eq_true hn
        have fields : as=bs := listEq_sound (fun _ _ hp=>ih hp) hs
        rw [names,fields]
      case aggregate.aggregate as bs =>
        exact congrArg Value.aggregate (listEq_sound (fun _ _ hp=>ih hp) h)
      case pointer.pointer a wa b wb =>
        obtain ⟨rfl,rfl⟩ := of_decide_eq_true h
        rfl

def optionEq (fuel : Nat) : Option Value → Option Value → Bool
  | none,none => true
  | some a,some b => valueEq fuel a b
  | _,_ => false

theorem optionEq_sound {fuel : Nat} {a b : Option Value} (h : optionEq fuel a b = true) : a=b := by
  cases a with
  | none => cases b <;> simp_all [optionEq]
  | some a =>
      cases b with
      | none => simp [optionEq] at h
      | some b => exact congrArg some (valueEq_sound fuel h)

def objectEq (fuel : Nat) (a b : Object) : Bool :=
  decide (a.type=b.type ∧ a.isArray=b.isArray ∧ a.writable=b.writable) &&
    listEq (optionEq fuel) a.cells b.cells

theorem objectEq_sound {fuel : Nat} {a b : Object} (h : objectEq fuel a b = true) : a=b := by
  obtain ⟨metadata,cells⟩ := split_and h
  obtain ⟨ht,ha,hw⟩ := of_decide_eq_true metadata
  have hc : a.cells=b.cells := listEq_sound (fun _ _ hp=>optionEq_sound (fuel:=fuel) hp) cells
  cases a
  cases b
  simp_all only

/-- Compare the complete heap and both environments, preserving the actual
returned Nat arena as a parameter. Its owner function is not decidably equal.
No claim about that arena is inferred or silently assumed from this check. -/
def stateEq (fuel : Nat) (a b : State) : Bool :=
  listEq (objectEq fuel) a.heap b.heap && decide (a.env=b.env ∧ a.globals=b.globals)

theorem stateEq_sound {fuel : Nat} {a b : State} (h : stateEq fuel a b = true) :
    a = {b with nats:=a.nats} := by
  obtain ⟨heap,metadata⟩ := split_and h
  have hh : a.heap=b.heap := listEq_sound (fun _ _ hp=>objectEq_sound (fuel:=fuel) hp) heap
  obtain ⟨he,hg⟩ := of_decide_eq_true metadata
  cases a
  cases b
  simp_all only

end ScopedC.StateWordEquality
