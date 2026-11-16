/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.TypedFrames

namespace ScopedC.ExpressionTemplates
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

 theorem call_one (cfg : Layout) (call : Call) {s mid after : State} {e : Expr} {v out : Value}
    {name : String} {fuel : Nat}
    (arg : evalExpr cfg call fuel s e = some (v,mid))
    (answer : call name [v] mid = some (out,after)) :
    evalExpr cfg call (fuel+1) s (.call (.var name) [e]) = some (out,after) := by
  rw [evalExpr]
  simp [List.foldlM,arg,answer]

 theorem call_two (cfg : Layout) (call : Call) {s mid before after : State}
    {a b : Expr} {v w out : Value} {name : String} {fuel : Nat}
    (left : evalExpr cfg call fuel s a = some (v,mid))
    (right : evalExpr cfg call fuel mid b = some (w,before))
    (answer : call name [v,w] before = some (out,after)) :
    evalExpr cfg call (fuel+1) s (.call (.var name) [a,b]) = some (out,after) := by
  rw [evalExpr]
  simp [List.foldlM,left,right,answer]

 theorem conditional (cfg : Layout) (call : Call) {s mid after : State}
    {test yes no : Expr} {condition value : Value} {fuel : Nat}
    (check : evalExpr cfg call fuel s test = some (condition,mid))
    (branch : evalExpr cfg call fuel mid (if truth condition then yes else no) = some (value,after)) :
    evalExpr cfg call (fuel+1) s (.conditional test yes no) = some (value,after) := by
  rw [evalExpr,check]
  exact branch

 theorem cast (cfg : Layout) (call : Call) {s mid : State} {e : Expr} {v represented : Value}
    {type : String} {fuel : Nat} (child : evalExpr cfg call fuel s e = some (v,mid))
    (convert : castValue cfg mid 100 type v = some represented) :
    evalExpr cfg call (fuel+1) s (.cast type e) = some (represented,mid) := by
  rw [evalExpr,child]
  simp [convert]

 theorem field (cfg : Layout) (call : Call) {s mid : State} {e : Expr} {v out : Value}
    {name : String} {fuel : Nat} (child : evalExpr cfg call fuel s e = some (v,mid))
    (lookup : nested cfg v [name] = some out) :
    evalExpr cfg call (fuel+1) s (.field "." e name) = some (out,mid) := by
  rw [evalExpr,child]
  simp [lookup]

 theorem record_two (cfg : Layout) (call : Call) {s mid after : State}
    {a b : Expr} {v w : Value} {fuel : Nat}
    (left : evalExpr cfg call fuel s a = some (v,mid))
    (right : evalExpr cfg call fuel mid b = some (w,after)) :
    evalExpr cfg call (fuel+1) s (.record [a,b]) = some (.aggregate [v,w],after) := by
  rw [evalExpr]
  simp [List.foldlM,left,right]

end ScopedC.ExpressionTemplates
