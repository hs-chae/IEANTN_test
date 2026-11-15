/- Parameterized additive stdio source semantics. Existing pure source
executions are reused through their complete finite execution trees. -/
import ScopedIO.WorldSource
import ScopedC.ArrayLegacyLift

namespace ScopedIO.WorldSourceWith
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedIO.WorldIO
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def SourceCall (cfg : Layout) (code : List Function) (p : WorldIO.Platform)
    (external : WorldIO.Call) :
    Nat → String → List Value → World → Value → World → Prop
  | 0,name,args,s,v,t => external name args s = some (v,t)
  | rank+1,name,args,s,v,t =>
      external name args s = some (v,t) ∨
      (∃ oldRank, ArraySourceCalls.SourceCall cfg code oldRank name args s.app v t.app ∧
        t.stream = s.stream) ∨
      ∃ f, f∈code ∧ f.name = name ∧
        ∃ pure : Machine.Call, (∀ called actual start value final,
          pure called actual start = some (value,final) →
          ∃ oldRank, ArraySourceCalls.SourceCall cfg code oldRank called actual start value final) ∧
        ∃ service : WorldIO.Call, (∀ called actual start value final,
          service called actual start = some (value,final) →
          SourceCall cfg code p external rank called actual start value final) ∧
        ∃ frame, bindArgs cfg f.parameters args s.app = some frame ∧
          ∃ outcome, WorldSource.Run cfg pure service p f.body ⟨frame,s.stream⟩ outcome ∧
            WorldSource.Finish cfg f s outcome v t

theorem pure_call {cfg : Layout} {code : List Function} {p : WorldIO.Platform}
    {external : WorldIO.Call} {rank oldRank : Nat} {name : String}
    {args : List Value} {s t : State} {v : Value}
    (h : ArraySourceCalls.SourceCall cfg code oldRank name args s v t) (stream : Stream) :
    SourceCall cfg code p external (rank+1) name args ⟨s,stream⟩ v ⟨t,stream⟩ :=
  Or.inr (Or.inl ⟨oldRank,h,rfl⟩)

theorem legacy_call {cfg : Layout} {code : List Function} {p : WorldIO.Platform}
    {external : WorldIO.Call} {rank oldRank : Nat} {name : String}
    {args : List Value} {s t : State} {v : Value}
    (h : SourceCalls.SourceCall cfg code oldRank name args s v t) (stream : Stream) :
    SourceCall cfg code p external (rank+1) name args ⟨s,stream⟩ v ⟨t,stream⟩ :=
  pure_call (ArrayLegacyLift.source_call h) stream

theorem external_call {cfg : Layout} {code : List Function} {p : WorldIO.Platform}
    {external : WorldIO.Call} {rank : Nat} {name : String}
    {args : List Value} {s t : World} {v : Value}
    (h : external name args s = some (v,t)) :
    SourceCall cfg code p external rank name args s v t := by
  cases rank with
  | zero => exact h
  | succ rank => exact Or.inl h

theorem installed_call {cfg : Layout} {code : List Function} {p : WorldIO.Platform}
    {external : WorldIO.Call} {rank : Nat} {name : String} {args : List Value}
    {s t : World} {v : Value} (f : Function) (installed : f∈code) (named : f.name = name)
    (pure : Machine.Call) (pure_closed : ∀ called actual start value final,
      pure called actual start = some (value,final) →
      ∃ oldRank, ArraySourceCalls.SourceCall cfg code oldRank called actual start value final)
    (service : WorldIO.Call) (service_closed : ∀ called actual start value final,
      service called actual start = some (value,final) →
      SourceCall cfg code p external rank called actual start value final)
    (frame : State) (arguments : bindArgs cfg f.parameters args s.app = some frame)
    (outcome : Loops.Flow World Value)
    (run : WorldSource.Run cfg pure service p f.body ⟨frame,s.stream⟩ outcome)
    (finish : WorldSource.Finish cfg f s outcome v t) :
    SourceCall cfg code p external (rank+1) name args s v t :=
  Or.inr (Or.inr ⟨f,installed,named,pure,pure_closed,service,service_closed,
    frame,arguments,outcome,run,finish⟩)

end ScopedIO.WorldSourceWith
