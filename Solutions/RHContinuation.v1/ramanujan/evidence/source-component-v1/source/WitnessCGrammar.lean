/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. Authors: OpenAI (Codex). -/
import LCMSourcePV.RestrictedC
namespace LCMSourcePV.Witness.C

inductive Expr where
  | nat (value : Nat)
  | var (name : String)
  | unary (op : String) (arg : Expr)
  | post (op : String) (arg : Expr)
  | cast (type : String) (arg : Expr)
  | binary (op : String) (left right : Expr)
  | field (op : String) (object : Expr) (name : String)
  | index (object index : Expr)
  | call (function : Expr) (args : List Expr)
  | record (fields : List Expr)
  deriving Repr

structure Decl where
  type : String
  name : String
  value : Option Expr
  deriving Repr

inductive Stmt where
  | skip
  | sequence (body : List Stmt)
  | declare (decls : List Decl)
  | eval (expression : Expr)
  | returnStmt (expression : Expr)
  | branch (condition : Expr) (yes no : Stmt)
  | whileLoop (condition : Expr) (body : Stmt)
  | forLoop (initial : Stmt) (condition : Option Expr) (step : Expr) (body : Stmt)
  deriving Repr

structure Function where
  returnType : String
  name : String
  parameters : List (String × String)
  body : Stmt
  deriving Repr

def join (xs : List String) : String := String.intercalate "," xs

def renderExpr : Nat → Expr → Option String
  | 0, _ => none
  | n+1, .nat v => some (toString v)
  | n+1, .var name => some name
  | n+1, .unary op a => do return "("++op++(←renderExpr n a)++")"
  | n+1, .post op a => do return "("++(←renderExpr n a)++op++")"
  | n+1, .cast t a => do return "(("++t++")"++(←renderExpr n a)++")"
  | n+1, .binary op a b => do
      return "("++(←renderExpr n a)++op++(←renderExpr n b)++")"
  | n+1, .field op a f => do return "("++(←renderExpr n a)++op++f++")"
  | n+1, .index a i => do return "("++(←renderExpr n a)++"["++(←renderExpr n i)++"])"
  | n+1, .call f args => do
      return (←renderExpr n f)++"("++join (←args.mapM (renderExpr n))++")"
  | n+1, .record xs => do return "{"++join (←xs.mapM (renderExpr n))++"}"

def renderDecl (d : Decl) : Option String := do
  let value ← match d.value with
    | none => some ""
    | some e => (fun s => "="++s) <$> renderExpr 1000 e
  return d.type++" "++d.name++value

def renderStmt : Nat → Stmt → Option String
  | 0, _ => none
  | n+1, .skip => some ";"
  | n+1, .sequence body => do
      return "{"++String.intercalate "\n" (←body.mapM (renderStmt n))++"}"
  | n+1, .declare ds => do
      -- Split a multiple declaration into equivalent consecutive declarations.
      return String.intercalate "\n" ((←ds.mapM renderDecl).map (·++";"))
  | n+1, .eval e => do return (←renderExpr 1000 e)++";"
  | n+1, .returnStmt e => do return "return "++(←renderExpr 1000 e)++";"
  | n+1, .branch c a b => do
      return "if("++(←renderExpr 1000 c)++")"++(←renderStmt n a)++"else "++(←renderStmt n b)
  | n+1, .whileLoop c body => do
      return "while("++(←renderExpr 1000 c)++")"++(←renderStmt n body)
  | n+1, .forLoop initial condition step body => do
      let init ← renderStmt n initial
      let guard ← match condition with
        | none => some ""
        | some e => renderExpr 1000 e
      return "for("++init++guard++";"++(←renderExpr 1000 step)++")"++(←renderStmt n body)

def renderFunction (f : Function) : Option String := do
  return f.returnType++" "++f.name++"("++
    join (f.parameters.map fun (t,n)=>t++" "++n)++")"++(←renderStmt 1000 f.body)++"\n"

def renderFunctions (fs : List Function) : Option String := do
  return String.intercalate "\n" (←fs.mapM renderFunction)

end LCMSourcePV.Witness.C
