/- Installed old source-body trees remain valid in an actual code extension.
No application-success premise or expected output is introduced. -/
import ScopedIO.WorldSource
namespace ScopedC.ArraySourceCalls
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem code_extension {cfg : Layout} {small large : List Function}
    (included : ∀ f, f ∈ small → f ∈ large)
    {rank : Nat} {name : String} {args : List Value} {s t : State} {v : Value}
    (run : SourceCall cfg small rank name args s v t) :
    SourceCall cfg large rank name args s v t := by
  induction rank generalizing name args s t v with
  | zero => exact run
  | succ rank ih =>
    rcases run with runtime | ⟨f,installed,named,service,closed,frame,bound,outcome,body,finish⟩
    · exact Or.inl runtime
    · exact Or.inr ⟨f,included f installed,named,service,
        fun called actual start value final source => ih (closed called actual start value final source),
        frame,bound,outcome,body,finish⟩

#print axioms code_extension
end ScopedC.ArraySourceCalls

namespace ScopedIO.WorldSource
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedIO.WorldIO
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem code_extension {cfg : Layout} {small large : List Function}
    (included : ∀ f, f ∈ small → f ∈ large)
    {platform : Platform} {fault : FaultPolicy} {rank : Nat}
    {name : String} {args : List Value} {s t : World} {v : Value}
    (run : SourceCall cfg small platform fault rank name args s v t) :
    SourceCall cfg large platform fault rank name args s v t := by
  induction rank generalizing name args s t v with
  | zero => exact run
  | succ rank ih =>
    rcases run with runtime | pure | body
    · exact Or.inl runtime
    · obtain ⟨oldRank,old,stream⟩ := pure
      exact Or.inr (Or.inl ⟨oldRank,ArraySourceCalls.code_extension included old,stream⟩)
    · obtain ⟨f,installed,named,pure,pureClosed,service,closed,frame,bound,outcome,body,finish⟩ := body
      refine Or.inr (Or.inr ⟨f,included f installed,named,pure,?_,service,?_,
        frame,bound,outcome,body,finish⟩)
      · intro called actual start value final source
        obtain ⟨oldRank,old⟩ := pureClosed called actual start value final source
        exact ⟨oldRank,ArraySourceCalls.code_extension included old⟩
      · intro called actual start value final source
        exact ih (closed called actual start value final source)

#print axioms code_extension
end ScopedIO.WorldSource
