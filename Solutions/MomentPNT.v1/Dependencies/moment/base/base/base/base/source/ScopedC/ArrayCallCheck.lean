/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.ArraySourceCallExecute
import ScopedC.StateWordEquality

namespace ScopedC.ArrayCallCheck
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Compare all application memory after a successful void call. The actual
Nat arena is retained; no arena equality or application output is assumed. -/
def hasState (result : Option (Value × State)) (cache : State) : Bool :=
  match result with
  | some (.unit,t) => StateWordEquality.stateEq 16 t cache
  | _ => false

theorem hasState_sound {result : Option (Value × State)} {cache : State}
    (h : hasState result cache = true) :
    ∃ t, result = some (.unit,t) ∧ t = {cache with nats:=t.nats} := by
  cases result with
  | none => simp [hasState] at h
  | some pair =>
    rcases pair with ⟨v,t⟩
    cases v <;> simp only [hasState] at h
    all_goals first | contradiction | skip
    exact ⟨t,rfl,StateWordEquality.stateEq_sound h⟩

theorem source_of_checked {cfg : Layout} {code : List Function}
    {expressionFuel statementFuel rank : Nat} {name : String} {args : List Value}
    {initial cache : State}
    (h : hasState (ArraySourceCallExecute.execute cfg code expressionFuel statementFuel rank
      name args initial) cache = true) :
    ∃ t, ArraySourceCalls.SourceCall cfg code rank name args initial .unit t ∧
      t = {cache with nats:=t.nats} := by
  obtain ⟨t,run,eqt⟩ := hasState_sound h
  exact ⟨t,ArraySourceCallExecute.execute_sound run,eqt⟩

end ScopedC.ArrayCallCheck
