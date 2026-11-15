/- Executable actual-body calls for the additive text world. Every reusable
pure callback carries an actual C-source proof; every effectful application
call runs its installed body. There is no application output oracle. -/
import ScopedIO.TextExecute
import ScopedC.ArraySourceCallExecute

namespace ScopedIO.TextCallExecute
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedIO.WorldIO
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def finish (cfg : Layout) (f : Function) (caller : World) :
    TextExecute.Outcome → Option (Value × World)
  | .returned final value => do
      let v ← castValue cfg final.app 100 f.returnType value
      return (v,WorldSource.pop caller final)
  | .continuing final =>
      if normalizeType f.returnType = "void"
      then some (.unit,WorldSource.pop caller final) else none

theorem finish_sound {cfg : Layout} {f : Function} {caller : World}
    {outcome : TextExecute.Outcome} {v : Value} {t : World}
    (h : finish cfg f caller outcome = some (v,t)) :
    WorldSource.Finish cfg f caller outcome v t := by
  cases outcome with
  | returned final value =>
    cases hc : castValue cfg final.app 100 f.returnType value with
    | none => simp [finish,hc] at h
    | some answer =>
      simp only [finish,hc,Bind.bind,Option.bind,Pure.pure,
        Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨hc,rfl⟩
  | continuing final =>
    by_cases hv : normalizeType f.returnType = "void"
    · simp only [finish,if_pos hv,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨hv,rfl,rfl⟩
    · simp [finish,hv] at h

def once (cfg : Layout) (code : List Function) (p : WorldIO.Platform)
    (external : WorldIO.Call) (expressionFuel statementFuel : Nat)
    (pureCall : Machine.Call) (service : WorldIO.Call) : WorldIO.Call := fun name args s =>
  match external name args s with
  | some result => some result
  | none =>
    match pureCall name args s.app with
    | some (v,t) => some (v,⟨t,s.stream⟩)
    | none => do
      let f ← ArraySourceCallExecute.find code name
      let frame ← bindArgs cfg f.parameters args s.app
      let outcome ← TextExecute.statement cfg pureCall service p expressionFuel statementFuel
        f.body ⟨frame,s.stream⟩
      finish cfg f s outcome

theorem once_sound {cfg : Layout} {code : List Function} {p : WorldIO.Platform}
    {external : WorldIO.Call} {expressionFuel statementFuel rank : Nat}
    {pureCall : Machine.Call} {service : WorldIO.Call}
    (pure_closed : ∀ name args s v t, pureCall name args s = some (v,t) →
      ∃ oldRank, ArraySourceCalls.SourceCall cfg code oldRank name args s v t)
    (world_closed : ∀ name args s v t, service name args s = some (v,t) →
      WorldSourceWith.SourceCall cfg code p external rank name args s v t)
    {name : String} {args : List Value} {s t : World} {v : Value}
    (h : once cfg code p external expressionFuel statementFuel pureCall service name args s =
      some (v,t)) :
    WorldSourceWith.SourceCall cfg code p external (rank+1) name args s v t := by
  cases hr : external name args s with
  | some result =>
    simp only [once,hr,Option.some.injEq] at h
    subst result
    exact WorldSourceWith.external_call hr
  | none =>
    cases hp : pureCall name args s.app with
    | some pair =>
      rcases pair with ⟨value,after⟩
      simp only [once,hr,hp,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      obtain ⟨oldRank,body⟩ := pure_closed _ _ _ _ _ hp
      exact WorldSourceWith.pure_call body s.stream
    | none =>
      cases hf : ArraySourceCallExecute.find code name with
      | none => simp [once,hr,hp,hf] at h
      | some f =>
        cases hb : bindArgs cfg f.parameters args s.app with
        | none => simp [once,hr,hp,hf,hb] at h
        | some frame =>
          cases ho : TextExecute.statement cfg pureCall service p expressionFuel statementFuel
              f.body ⟨frame,s.stream⟩ with
          | none => simp [once,hr,hp,hf,hb,ho] at h
          | some outcome =>
            simp only [once,hr,hp,hf,hb,ho,Bind.bind,Option.bind] at h
            obtain ⟨installed,named⟩ := ArraySourceCallExecute.find_sound hf
            exact WorldSourceWith.installed_call f installed named pureCall pure_closed
              service world_closed frame hb outcome (TextExecute.statement_sound ho)
              (finish_sound h)

def execute (cfg : Layout) (code : List Function) (p : WorldIO.Platform)
    (external : WorldIO.Call) (expressionFuel statementFuel : Nat)
    (pureCall : Machine.Call) : Nat → WorldIO.Call
  | 0 => external
  | rank+1 => once cfg code p external expressionFuel statementFuel pureCall
      (execute cfg code p external expressionFuel statementFuel pureCall rank)

theorem execute_sound {cfg : Layout} {code : List Function} {p : WorldIO.Platform}
    {external : WorldIO.Call} {expressionFuel statementFuel : Nat} {pureCall : Machine.Call}
    (pure_closed : ∀ name args s v t, pureCall name args s = some (v,t) →
      ∃ oldRank, ArraySourceCalls.SourceCall cfg code oldRank name args s v t)
    {rank : Nat} {name : String} {args : List Value} {s t : World} {v : Value}
    (h : execute cfg code p external expressionFuel statementFuel pureCall rank name args s =
      some (v,t)) :
    WorldSourceWith.SourceCall cfg code p external rank name args s v t := by
  induction rank generalizing name args s v t with
  | zero => exact h
  | succ rank ih => exact once_sound pure_closed (fun _ _ _ _ _ hp => ih hp) h

end ScopedIO.TextCallExecute
