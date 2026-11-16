/- Assemble actual installed bodies in the additive I/O world. Both pure
and world callbacks retain complete actual-source proof obligations. -/
import ScopedIO.WorldSource
namespace ScopedIO.WorldSource
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedIO.WorldIO
set_option autoImplicit false
set_option maxHeartbeats 0

theorem installed_body {cfg : Layout} {code : List Function} {p : WorldIO.Platform}
    {fault : WorldIO.FaultPolicy} {rank : Nat} {f : Function}
    {args : List Value} {s t : World} {v : Value} {frame : State}
    {pure : Machine.Call} {service : WorldIO.Call} {outcome : Loops.Flow World Value}
    (installed : f∈code)
    (pureClosed : ∀ name actual start value final,pure name actual start=some (value,final) →
      ∃ oldRank,ArraySourceCalls.SourceCall cfg code oldRank name actual start value final)
    (worldClosed : ∀ name actual start value final,service name actual start=some (value,final) →
      SourceCall cfg code p fault rank name actual start value final)
    (arguments : bindArgs cfg f.parameters args s.app=some frame)
    (body : Run cfg pure service p f.body ⟨frame,s.stream⟩ outcome)
    (finish : Finish cfg f s outcome v t) :
    SourceCall cfg code p fault (rank+1) f.name args s v t :=
  Or.inr (Or.inr ⟨f,installed,rfl,pure,pureClosed,service,worldClosed,frame,arguments,outcome,body,finish⟩)

#print axioms installed_body
end ScopedIO.WorldSource
