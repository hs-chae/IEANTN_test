/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.SourceCalls

namespace ScopedIO
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The existing expression, typed memory and statement semantics are reused
unchanged. The external platform contract is a parameter, not an application
execution oracle. An I/O extension must implement only documented generic
stdio effects and retain the original Nat ABI boundary. -/
def SourceWith (external : Call) (cfg : Layout) (code : List Function) :
    Nat → String → List Value → State → Value → State → Prop
  | 0,name,args,s,v,t => external name args s = some (v,t)
  | rank+1,name,args,s,v,t =>
    external name args s = some (v,t) ∨
    ∃ f, f ∈ code ∧ f.name = name ∧
      ∃ service : Call,
        (∀ called actual start value final,
          service called actual start = some (value,final) →
          SourceWith external cfg code rank called actual start value final) ∧
        ∃ frame, bindArgs cfg f.parameters args s = some frame ∧
          ∃ outcome, Run cfg service f.body frame outcome ∧ Finish cfg f s outcome v t

theorem external_leaf {external : Call} {cfg : Layout} {code : List Function} {rank : Nat}
    {name : String} {args : List Value} {s t : State} {v : Value}
    (h : external name args s = some (v,t)) :
    SourceWith external cfg code rank name args s v t := by
  cases rank with
  | zero => exact h
  | succ rank => exact Or.inl h

theorem installed_body {external : Call} {cfg : Layout} {code : List Function} {rank : Nat}
    {f : Function} {args : List Value} {s frame t : State} {v : Value}
    {service : Call} {outcome : Loops.Flow State Value}
    (installed : f ∈ code)
    (closed : ∀ called actual start value final,
      service called actual start = some (value,final) →
      SourceWith external cfg code rank called actual start value final)
    (arguments : bindArgs cfg f.parameters args s = some frame)
    (body : Run cfg service f.body frame outcome)
    (finish : Finish cfg f s outcome v t) :
    SourceWith external cfg code (rank+1) f.name args s v t :=
  Or.inr ⟨f,installed,rfl,service,closed,frame,arguments,outcome,body,finish⟩

/-- Every previously proved pure application body transports without any
reproof or new application assumption when its generic runtime is included. -/
theorem lift_pure {external : Call} {cfg : Layout} {code : List Function} {rank : Nat}
    (runtime_included : ∀ name args s v t,
      RuntimeCore.call name args s = some (v,t) → external name args s = some (v,t))
    {name : String} {args : List Value} {s t : State} {v : Value}
    (h : SourceCall cfg code rank name args s v t) :
    SourceWith external cfg code rank name args s v t := by
  induction rank generalizing name args s t v with
  | zero => exact runtime_included name args s v t h
  | succ rank ih =>
    rcases h with runtime | ⟨f,installed,named,service,closed,frame,bound,outcome,body,finish⟩
    · exact external_leaf (runtime_included name args s v t runtime)
    · exact Or.inr ⟨f,installed,named,service,
        fun called actual start value final call => ih (closed called actual start value final call),
        frame,bound,outcome,body,finish⟩

theorem original_boundary {cfg : Layout} {code : List Function} {rank : Nat}
    {name : String} {args : List Value} {s t : State} {v : Value} :
    SourceWith RuntimeCore.call cfg code rank name args s v t ↔
      SourceCall cfg code rank name args s v t := by
  induction rank generalizing name args s t v with
  | zero => rfl
  | succ rank ih =>
    constructor
    · intro h
      rcases h with runtime | ⟨f,installed,named,service,closed,frame,bound,outcome,body,finish⟩
      · exact runtime_leaf runtime
      · exact Or.inr ⟨f,installed,named,service,
          fun called actual start value final call => ih.mp (closed called actual start value final call),
          frame,bound,outcome,body,finish⟩
    · exact lift_pure (fun _ _ _ _ _ h => h)

end ScopedIO
