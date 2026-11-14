/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.ExpressionTemplates

namespace ScopedC.DeclarationReturn
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Exact source `T name = initializer; return name;`. Initialization evaluates
 the actual expression before allocating the fresh local cell. -/
theorem body (cfg : Layout) (call : Call) (type name : String) (initializer : Expr)
    {before after : State} {raw represented : Value}
    (expression : evalExpr cfg call 1000 before initializer = some (raw,after))
    (convert : castValue cfg after 100 type raw = some represented)
    (init : initialized 1000 represented = true)
    (h0 : name ≠ "true") (h1 : name ≠ "false") (h2 : name ≠ "nullptr") (h3 : name ≠ "NULL") :
    Run cfg call (.sequence [.declare [{type:=type,name:=name,value:=some initializer,arrayExtent:=none}],
      .returnStmt (.var name)]) before
      (.returned (popScope before (allocate after type name (some represented))) represented) := by
  have declared : Declare cfg call [{type:=type,name:=name,value:=some initializer,arrayExtent:=none}]
      before (allocate after type name (some represented)) := by
    simp [Declare,declarations,List.foldlM,expression,convert]
  apply Loops.StmtRun.sequence (Loops.SeqRun.next (Loops.StmtRun.declare declared)
    (Loops.SeqRun.returned (Loops.StmtRun.returnValue
      ⟨2,TypedFrames.allocate_eval cfg call 1 after type name represented init h0 h1 h2 h3⟩)))
  exact ⟨rfl,rfl⟩

end ScopedC.DeclarationReturn
