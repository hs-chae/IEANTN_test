/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.WordService

namespace SynergyC.ArgumentConversion
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0

/-- C parameter conversion is performed by bindArgs. Replacing raw argument
representations is valid only when every actual matching installed function
produces exactly the same initialized parameter frame. -/
theorem replace_arguments {cfg : Layout} {code : List Function} {rank : Nat}
    {name : String} {args raw : List Value} {s t : State} {v : Value}
    (h : SourceCall cfg code (rank+1) name args s v t)
    (notRuntime : RuntimeCore.call name args s = none)
    (sameFrames : ∀ f ∈ code, f.name = name →
      bindArgs cfg f.parameters raw s = bindArgs cfg f.parameters args s) :
    SourceCall cfg code (rank+1) name raw s v t := by
  rcases h with runtime | ⟨f,installed,named,service,closed,frame,bound,outcome,body,finish⟩
  · rw [notRuntime] at runtime
    contradiction
  · exact Or.inr ⟨f,installed,named,service,closed,frame,
      (sameFrames f installed named).trans bound,outcome,body,finish⟩

end SynergyC.ArgumentConversion
