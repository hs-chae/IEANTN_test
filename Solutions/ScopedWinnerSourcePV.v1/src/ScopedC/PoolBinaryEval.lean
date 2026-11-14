/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolExpressions
namespace ScopedC.PoolCalls
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
 theorem eval_binary_plain {op : String} {fuel : Nat} {s t u : State}
    {lhs rhs : Expr} {a b result : Value} (call : Call)
    (h0 : op ≠ "=") (h1 : op ≠ ",") (h2 : op ≠ "&&") (h3 : op ≠ "||")
    (left : evalExpr Header.layout call fuel s lhs = some (a,t))
    (right : evalExpr Header.layout call fuel t rhs = some (b,u))
    (answer : binaryValue Header.layout u op a b = some result) :
    evalExpr Header.layout call (fuel+1) s (.binary op lhs rhs) = some (result,u) := by
  rw [evalExpr]
  simp only [left,right,answer,bind,Option.bind]
  rfl
  all_goals assumption
end ScopedC.PoolCalls
