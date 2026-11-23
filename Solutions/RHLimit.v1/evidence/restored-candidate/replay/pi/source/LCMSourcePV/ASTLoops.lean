/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WitnessCGrammar

namespace LCMSourcePV.ASTLoops
open LCMSourcePV.Witness.C
universe u v

inductive Flow (State : Type u) (Value : Type v) where
  | continuing (state : State)
  | returned (state : State) (value : Value)

/-- An omitted C for-condition is true. A present condition executes its
actual expression, including any effects, before testing the resulting value. -/
inductive GuardRun {State : Type u} {Value : Type v}
    (Eval : Expr → State → State → Value → Prop) (truth : Value → Bool) :
    Option Expr → State → State → Bool → Prop
  | omitted (s : State) : GuardRun Eval truth none s s true
  | present {e s t value} (run : Eval e s t value) :
      GuardRun Eval truth (some e) s t (truth value)

mutual
  /-- Structural execution of actual C statement trees. Expressions and
  declarations are supplied by concrete typed word/memory semantics. No rule
  mentions a selected function name or an expected complete function body. -/
  inductive StmtRun {State : Type u} {Value : Type v}
      (Eval : Expr → State → State → Value → Prop)
      (Declare : List Decl → State → State → Prop) (truth : Value → Bool)
      (Scope : State → Flow State Value → Flow State Value → Prop) :
      Stmt → State → Flow State Value → Prop
    | skip (s : State) : StmtRun Eval Declare truth Scope .skip s (.continuing s)
    | evaluate {e s t value} (run : Eval e s t value) :
        StmtRun Eval Declare truth Scope (.eval e) s (.continuing t)
    | declare {decls s t} (run : Declare decls s t) :
        StmtRun Eval Declare truth Scope (.declare decls) s (.continuing t)
    | returnValue {e s t value} (run : Eval e s t value) :
        StmtRun Eval Declare truth Scope (.returnStmt e) s (.returned t value)
    | branch {e yes no s t value result} (test : Eval e s t value)
        (body : StmtRun Eval Declare truth Scope (if truth value then yes else no) t result) :
        StmtRun Eval Declare truth Scope (.branch e yes no) s result
    | sequence {body s inner result} (run : SeqRun Eval Declare truth Scope body s inner)
        (exitScope : Scope s inner result) :
        StmtRun Eval Declare truth Scope (.sequence body) s result
    | forLoop {init cond step body s t inner result}
        (initialization : StmtRun Eval Declare truth Scope init s (.continuing t))
        (loop : ForRun Eval Declare truth Scope cond step body t inner)
        (exitScope : Scope s inner result) :
        StmtRun Eval Declare truth Scope (.forLoop init cond step body) s result
    | forInitialReturn {init cond step body s t value result}
        (initialization : StmtRun Eval Declare truth Scope init s (.returned t value))
        (exitScope : Scope s (.returned t value) result) :
        StmtRun Eval Declare truth Scope (.forLoop init cond step body) s result
    | whileLoop {cond body s result} (loop : WhileRun Eval Declare truth Scope cond body s result) :
        StmtRun Eval Declare truth Scope (.whileLoop cond body) s result

  inductive SeqRun {State : Type u} {Value : Type v}
      (Eval : Expr → State → State → Value → Prop)
      (Declare : List Decl → State → State → Prop) (truth : Value → Bool)
      (Scope : State → Flow State Value → Flow State Value → Prop) :
      List Stmt → State → Flow State Value → Prop
    | nil (s : State) : SeqRun Eval Declare truth Scope [] s (.continuing s)
    | next {head tail s t result}
        (first : StmtRun Eval Declare truth Scope head s (.continuing t))
        (rest : SeqRun Eval Declare truth Scope tail t result) :
        SeqRun Eval Declare truth Scope (head::tail) s result
    | returned {head tail s t value}
        (first : StmtRun Eval Declare truth Scope head s (.returned t value)) :
        SeqRun Eval Declare truth Scope (head::tail) s (.returned t value)

  inductive ForRun {State : Type u} {Value : Type v}
      (Eval : Expr → State → State → Value → Prop)
      (Declare : List Decl → State → State → Prop) (truth : Value → Bool)
      (Scope : State → Flow State Value → Flow State Value → Prop) :
      Option Expr → Expr → Stmt → State → Flow State Value → Prop
    | done {cond step body s t} (test : GuardRun Eval truth cond s t false) :
        ForRun Eval Declare truth Scope cond step body s (.continuing t)
    | next {cond step body s t b c value result}
        (test : GuardRun Eval truth cond s t true)
        (iteration : StmtRun Eval Declare truth Scope body t (.continuing b))
        (increment : Eval step b c value)
        (rest : ForRun Eval Declare truth Scope cond step body c result) :
        ForRun Eval Declare truth Scope cond step body s result
    | returned {cond step body s t b value}
        (test : GuardRun Eval truth cond s t true)
        (iteration : StmtRun Eval Declare truth Scope body t (.returned b value)) :
        ForRun Eval Declare truth Scope cond step body s (.returned b value)

  inductive WhileRun {State : Type u} {Value : Type v}
      (Eval : Expr → State → State → Value → Prop)
      (Declare : List Decl → State → State → Prop) (truth : Value → Bool)
      (Scope : State → Flow State Value → Flow State Value → Prop) :
      Expr → Stmt → State → Flow State Value → Prop
    | done {cond body s t value} (test : Eval cond s t value) (stop : truth value=false) :
        WhileRun Eval Declare truth Scope cond body s (.continuing t)
    | next {cond body s t b value result}
        (test : Eval cond s t value) (keepGoing : truth value=true)
        (iteration : StmtRun Eval Declare truth Scope body t (.continuing b))
        (rest : WhileRun Eval Declare truth Scope cond body b result) :
        WhileRun Eval Declare truth Scope cond body s result
    | returned {cond body s t b condition value}
        (test : Eval cond s t condition) (keepGoing : truth condition=true)
        (iteration : StmtRun Eval Declare truth Scope body t (.returned b value)) :
        WhileRun Eval Declare truth Scope cond body s (.returned b value)
end

end LCMSourcePV.ASTLoops
