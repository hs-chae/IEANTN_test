/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.ArraySourceExecute

namespace ScopedC.ArraySourceCallExecute
open ScopedC.Syntax ScopedC.Machine ScopedC.ArraySourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0

def find : List Function → String → Option Function
  | [],_ => none
  | f::fs,name => if f.name = name then some f else find fs name

theorem find_sound {code : List Function} {name : String} {f : Function}
    (h : find code name = some f) : f ∈ code ∧ f.name = name := by
  induction code with
  | nil => simp [find] at h
  | cons first rest ih =>
      by_cases hn : first.name = name
      · simp only [find,if_pos hn,Option.some.injEq] at h
        subst f
        exact ⟨List.mem_cons_self,hn⟩
      · simp only [find,if_neg hn] at h
        obtain ⟨hm,he⟩ := ih h
        exact ⟨List.mem_cons_of_mem first hm,he⟩

def finish (cfg : Layout) (f : Function) (caller : State) :
    ArraySourceExecute.Outcome → Option (Value × State)
  | .returned final value => do
      let v ← castValue cfg final 100 f.returnType value
      pure (v,popScope caller final)
  | .continuing final =>
      if normalizeType f.returnType = "void" then some (.unit,popScope caller final) else none

theorem finish_sound {cfg : Layout} {f : Function} {caller : State}
    {outcome : ArraySourceExecute.Outcome} {v : Value} {t : State}
    (h : finish cfg f caller outcome = some (v,t)) : Finish cfg f caller outcome v t := by
  cases outcome with
  | returned final value =>
      cases hc : castValue cfg final 100 f.returnType value with
      | none => simp [finish,hc] at h
      | some w =>
          simp only [finish,hc,Bind.bind,Option.bind,Pure.pure,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl⟩
          exact ⟨hc,rfl⟩
  | continuing final =>
      by_cases hv : normalizeType f.returnType = "void"
      · simp only [finish,if_pos hv,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨hv,rfl,rfl⟩
      · simp [finish,hv] at h

/-- Runtime leaves are exactly the old enumerated generic ABI. Every other
successful call binds the actual source parameters and executes the actual
installed statement tree. There is no application-specific dispatch. -/
def once (cfg : Layout) (code : List Function) (expressionFuel statementFuel : Nat)
    (service : Call) : Call := fun name args s =>
  match RuntimeCore.call name args s with
  | some result => some result
  | none => do
      let f ← find code name
      let frame ← bindArgs cfg f.parameters args s
      let outcome ← ArraySourceExecute.statement cfg service expressionFuel statementFuel f.body frame
      finish cfg f s outcome

theorem once_sound {cfg : Layout} {code : List Function} {expressionFuel statementFuel rank : Nat}
    {service : Call}
    (closed : ∀ name args s v t, service name args s = some (v,t) → SourceCall cfg code rank name args s v t)
    {name : String} {args : List Value} {s : State} {v : Value} {t : State}
    (h : once cfg code expressionFuel statementFuel service name args s = some (v,t)) :
    SourceCall cfg code (rank+1) name args s v t := by
  cases hr : RuntimeCore.call name args s with
  | some result =>
      simp only [once,hr,Option.some.injEq] at h
      subst result
      exact runtime_leaf hr
  | none =>
      cases hf : find code name with
      | none => simp [once,hr,hf] at h
      | some f =>
          cases hb : bindArgs cfg f.parameters args s with
          | none => simp [once,hr,hf,hb] at h
          | some frame =>
              cases ho : ArraySourceExecute.statement cfg service expressionFuel statementFuel f.body frame with
              | none => simp [once,hr,hf,hb,ho] at h
              | some outcome =>
                  simp only [once,hr,hf,hb,ho,Bind.bind,Option.bind] at h
                  obtain ⟨mem,named⟩ := find_sound hf
                  exact Or.inr ⟨f,mem,named,service,closed,frame,hb,outcome,
                    ArraySourceExecute.statement_sound ho,finish_sound h⟩

def execute (cfg : Layout) (code : List Function) (expressionFuel statementFuel : Nat) : Nat → Call
  | 0 => RuntimeCore.call
  | rank+1 => once cfg code expressionFuel statementFuel (execute cfg code expressionFuel statementFuel rank)

theorem execute_sound {cfg : Layout} {code : List Function} {expressionFuel statementFuel : Nat}
    {rank : Nat} {name : String} {args : List Value} {s : State} {v : Value} {t : State}
    (h : execute cfg code expressionFuel statementFuel rank name args s = some (v,t)) :
    SourceCall cfg code rank name args s v t := by
  induction rank generalizing name args s v t with
  | zero => exact h
  | succ rank ih => exact once_sound (fun _ _ _ _ _ hp=>ih hp) h

end ScopedC.ArraySourceCallExecute
