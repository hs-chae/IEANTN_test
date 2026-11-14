/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceCallRanks

namespace ScopedC.CallEvents
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0

/-- A proof-only finite-call witness. The output is not a trusted application
 primitive: constructing the event requires an actual lower-rank source-body
 execution proof for exactly the input, full state and output recorded here. -/
structure Event (cfg : Layout) (code : List Function) (rank : Nat) where
  name : String
  args : List Value
  before : State
  value : Value
  after : State
  execution : SourceCall cfg code rank name args before value after

noncomputable def one {cfg : Layout} {code : List Function} {rank : Nat}
    (e : Event cfg code rank) : Call := by
  classical
  exact fun name args before =>
    if name = e.name ∧ args = e.args ∧ before = e.before then some (e.value,e.after) else none

theorem one_self {cfg : Layout} {code : List Function} {rank : Nat}
    (e : Event cfg code rank) : one e e.name e.args e.before = some (e.value,e.after) := by
  simp [one]

theorem one_other {cfg : Layout} {code : List Function} {rank : Nat}
    (e : Event cfg code rank) {name : String} (different : name ≠ e.name)
    (args : List Value) (before : State) : one e name args before = none := by
  simp [one,different]

theorem one_closed {cfg : Layout} {code : List Function} {rank : Nat}
    (e : Event cfg code rank) {name : String} {args : List Value} {s t : State} {v : Value}
    (h : one e name args s = some (v,t)) : SourceCall cfg code rank name args s v t := by
  unfold one at h
  split_ifs at h with sameInputs
  · rcases sameInputs with ⟨rfl,rfl,rfl⟩
    cases h
    exact e.execution

def append (first second : Call) : Call := fun name args before =>
  match first name args before with
  | some result => some result
  | none => second name args before

theorem append_left {first second : Call} {name : String} {args : List Value} {s t : State} {v : Value}
    (h : first name args s = some (v,t)) : append first second name args s = some (v,t) := by
  simp [append,h]

theorem append_right {first second : Call} {name : String} {args : List Value} {s t : State} {v : Value}
    (h0 : first name args s = none) (h1 : second name args s = some (v,t)) :
    append first second name args s = some (v,t) := by simp [append,h0,h1]

theorem append_closed {cfg : Layout} {code : List Function} {rank : Nat} {first second : Call}
    (left : ∀ name args s v t, first name args s = some (v,t) → SourceCall cfg code rank name args s v t)
    (right : ∀ name args s v t, second name args s = some (v,t) → SourceCall cfg code rank name args s v t)
    {name : String} {args : List Value} {s t : State} {v : Value}
    (h : append first second name args s = some (v,t)) : SourceCall cfg code rank name args s v t := by
  unfold append at h
  cases hl : first name args s with
  | none => exact right name args s v t (by simpa only [hl] using h)
  | some result =>
    simp only [hl,Option.some.injEq] at h
    cases h
    exact left name args s v t hl

end ScopedC.CallEvents
