/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceCalls

namespace ScopedC.SourceCalls
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Padding a finite execution tree changes no body, subcall, or result. -/
theorem raise_once {cfg : Layout} {code : List Function} {rank : Nat}
    {name : String} {args : List Value} {s t : State} {v : Value}
    (h : SourceCall cfg code rank name args s v t) :
    SourceCall cfg code (rank+1) name args s v t := by
  induction rank generalizing name args s t v with
  | zero => exact runtime_leaf h
  | succ rank ih =>
    rcases h with runtime | ⟨f,installed,named,service,closed,frame,bound,outcome,body,finish⟩
    · exact runtime_leaf runtime
    · exact Or.inr ⟨f,installed,named,service,
        fun called actual start value final call => ih (closed called actual start value final call),
        frame,bound,outcome,body,finish⟩

end ScopedC.SourceCalls
