/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.ExpressionTemplates

namespace ScopedC.ExpressionTemplates
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Only the ordinary binary-operator branch. Short-circuit and assignment
 have their distinct source rules; no side-effect commutation is assumed. -/
theorem binary (cfg : Layout) (call : Call) {op : String} {fuel : Nat}
    {s mid after : State} {lhs rhs : Expr} {a b result : Value}
    (h0 : op ≠ "=") (h1 : op ≠ ",") (h2 : op ≠ "&&") (h3 : op ≠ "||")
    (left : evalExpr cfg call fuel s lhs = some (a,mid))
    (right : evalExpr cfg call fuel mid rhs = some (b,after))
    (answer : binaryValue cfg after op a b = some result) :
    evalExpr cfg call (fuel+1) s (.binary op lhs rhs) = some (result,after) := by
  rw [evalExpr]
  simp only [left,right,answer,bind,Option.bind]
  rfl
  all_goals assumption

end ScopedC.ExpressionTemplates
