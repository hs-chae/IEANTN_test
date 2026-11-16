/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.ArraySourceCallExecute
import ScopedC.ArrayRank

namespace ScopedC.ContractExecute
open ScopedC.Syntax ScopedC.Machine ScopedC.ArraySourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Execute an actual installed body, with no external runtime leaves. This
is intended for the word-only C program. Unsupported external calls fail
closed. The original typed expression/statement/memory semantics is reused.
-/
def once (cfg : Layout) (code : List Function) (expressionFuel statementFuel : Nat)
    (service : Call) : Call := fun called args s => do
  let f ← ArraySourceCallExecute.find code called
  let frame ← bindArgs cfg f.parameters args s
  let outcome ← ArraySourceExecute.statement cfg service expressionFuel statementFuel f.body frame
  ArraySourceCallExecute.finish cfg f s outcome

theorem once_sound {cfg : Layout} {code : List Function}
    {expressionFuel statementFuel rank : Nat} {service : Call}
    (closed : ∀ name args s v t, service name args s = some (v,t) →
      SourceCall cfg code rank name args s v t)
    {name : String} {args : List Value} {s : State} {v : Value} {t : State}
    (h : once cfg code expressionFuel statementFuel service name args s = some (v,t)) :
    SourceCall cfg code (rank+1) name args s v t := by
  cases hf : ArraySourceCallExecute.find code name with
  | none => simp [once,hf] at h
  | some f =>
    cases hb : bindArgs cfg f.parameters args s with
    | none => simp [once,hf,hb] at h
    | some frame =>
      cases ho : ArraySourceExecute.statement cfg service expressionFuel statementFuel f.body frame with
      | none => simp [once,hf,hb,ho] at h
      | some outcome =>
        simp only [once,hf,hb,ho,Bind.bind,Option.bind] at h
        obtain ⟨mem,named⟩ := ArraySourceCallExecute.find_sound hf
        exact Or.inr ⟨f,mem,named,service,closed,frame,hb,outcome,
          ArraySourceExecute.statement_sound ho,ArraySourceCallExecute.finish_sound h⟩

/-- A verified function contract may replace repeated interpretation of its
body. It must have an actual-source execution proof for EVERY successful
answer, at the explicit contract rank. This is not an expected-output oracle.
The numerical C source, arithmetic and algorithms are unchanged. -/
def execute (cfg : Layout) (code : List Function) (expressionFuel statementFuel : Nat)
    (contract : Call) : Nat → Call
  | 0 => contract
  | fuel+1 => fun name args s =>
    match contract name args s with
    | some out => some out
    | none => once cfg code expressionFuel statementFuel
        (execute cfg code expressionFuel statementFuel contract fuel) name args s

theorem execute_sound {cfg : Layout} {code : List Function}
    {expressionFuel statementFuel contractRank : Nat} {contract : Call}
    (contractClosed : ∀ name args s v t, contract name args s = some (v,t) →
      SourceCall cfg code contractRank name args s v t)
    {fuel : Nat} {name : String} {args : List Value} {s : State} {v : Value} {t : State}
    (h : execute cfg code expressionFuel statementFuel contract fuel name args s = some (v,t)) :
    SourceCall cfg code (contractRank+fuel) name args s v t := by
  induction fuel generalizing name args s v t with
  | zero => exact contractClosed _ _ _ _ _ h
  | succ fuel ih =>
    cases hc : contract name args s with
    | some out =>
      simp only [execute,hc,Option.some.injEq] at h
      subst out
      exact ArrayRank.of_le (Nat.le_add_right contractRank (fuel+1))
        (contractClosed _ _ _ _ _ hc)
    | none =>
      simp only [execute,hc] at h
      exact once_sound (fun _ _ _ _ _ hp => ih hp) h

end ScopedC.ContractExecute
