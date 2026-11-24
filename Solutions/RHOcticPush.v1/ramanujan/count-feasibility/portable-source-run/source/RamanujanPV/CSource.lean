/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LCMSourcePV.RestrictedC

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RamanujanPV.Source

inductive Var where
  | n | d | a | den | p | start | tail | fuel | count | out


def varText : Var → String
  | .n => "n" | .d => "d" | .a => "a" | .den => "den" | .p => "p"
  | .start => "bound" | .tail => "tail" | .fuel => "fuel"
  | .count => "count" | .out => "out"

inductive Fn where
  | isPrime | next | cover


def fnText : Fn → String
  | .isPrime => "rpc_is_prime" | .next => "pc_next" | .cover => "rpc_count"

inductive Bin where
  | add | sub | mul | div | rem | lt | le | gt | eq | land | lor


def binText : Bin → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .rem => "%"
  | .lt => "<" | .le => "<=" | .gt => ">" | .eq => "=="
  | .land => "&&" | .lor => "||"

def precedence : Bin → Nat
  | .lor => 4 | .land => 5 | .eq => 8 | .lt | .le | .gt => 9
  | .add | .sub => 11 | .mul | .div | .rem => 12

inductive Expr where
  | lit (n : Nat) | var (v : Var) | maxWord
  | binary (op : Bin) (a b : Expr)
  | call1 (fn : Fn) (argument : Expr)
  | call2 (fn : Fn) (first second : Expr)


def joinStrings (separator : String) : List String → String
  | [] => ""
  | [text] => text
  | text::rest => text ++ separator ++ joinStrings separator rest

def exprText (context : Nat) : Expr → String
  | .lit n => toString n
  | .var v => varText v
  | .maxWord => "UINT64_MAX"
  | .binary op a b =>
    let level := precedence op
    let text := exprText level a ++ " " ++ binText op ++ " " ++ exprText (level+1) b
    if level<context then "(" ++ text ++ ")" else text
  | .call1 fn argument => fnText fn ++ "(" ++ exprText 0 argument ++ ")"
  | .call2 fn a b => fnText fn ++ "(" ++ exprText 0 a ++ ", " ++ exprText 0 b ++ ")"

inductive Update where
  | increment (v : Var) | decrement (v : Var)


def updateText : Update → String
  | .increment v => "++" ++ varText v
  | .decrement v => "--" ++ varText v

inductive Stmt where
  | empty
  | sequence (first second : Stmt)
  | declare (v : Var) (value : Expr)
  | assign (v : Var) (value : Expr)
  | store (base index value : Expr)
  | update (op : Update)
  | returnValue (value : Expr)
  | ifReturn (condition value : Expr)
  | whileLoop (condition : Expr) (body : Stmt)
  | forLoop (v : Var) (init condition : Expr) (step : Update) (body : Stmt)

def block : List Stmt → Stmt
  | [] => .empty
  | statement::rest => .sequence statement (block rest)


def stmtText : Stmt → String
  | .empty => ""
  | .sequence a b => stmtText a ++ "\n" ++ stmtText b
  | .declare v value => "uint64_t " ++ varText v ++ " = " ++ exprText 0 value ++ ";"
  | .assign v value => varText v ++ " = " ++ exprText 0 value ++ ";"
  | .store base index value => exprText 13 base ++ "[" ++ exprText 0 index ++ "] = " ++ exprText 0 value ++ ";"
  | .update op => updateText op ++ ";"
  | .returnValue value => "return " ++ exprText 0 value ++ ";"
  | .ifReturn condition value => "if (" ++ exprText 0 condition ++ ") return " ++ exprText 0 value ++ ";"
  | .whileLoop condition body => "while (" ++ exprText 0 condition ++ ") {\n" ++
      stmtText body ++ "\n}"
  | .forLoop v init condition step body => "for (uint64_t " ++ varText v ++ " = " ++
      exprText 0 init ++ "; " ++ exprText 0 condition ++ "; " ++ updateText step ++ ") {\n" ++
      stmtText body ++ "\n}"

structure Parameter where
  name : Var
  pointer : Bool


structure Function where
  name : Fn
  parameters : List Parameter
  body : Stmt


structure Program where
  unsignedWidth : Nat
  functions : List Function


def parameterText (p : Parameter) : String :=
  "uint64_t " ++ (if p.pointer then "*" else "") ++ varText p.name

def functionText (f : Function) : String :=
  "uint64_t " ++ fnText f.name ++ "(" ++ joinStrings ", " (f.parameters.map parameterText) ++
    ") {\n" ++ stmtText f.body ++ "\n}"

def render (program : Program) : Option String :=
  if program.unsignedWidth != 64 then none else
    some ("#include <stdint.h>\n\n" ++ joinStrings "\n\n" (program.functions.map functionText) ++ "\n")

open Expr Stmt Bin

def primeFunction : Function := ⟨.isPrime,[⟨.n,false⟩],block [
  .ifReturn (.binary .lt (.var .n) (.lit 2)) (.lit 0),
  .forLoop .d (.lit 2) (.binary .le (.var .d) (.binary .div (.var .n) (.var .d)))
    (.increment .d) (block [.ifReturn (.binary .eq (.binary .rem (.var .n) (.var .d)) (.lit 0)) (.lit 0)]),
  .returnValue (.lit 1)]⟩

def countFunction : Function := ⟨.cover,[⟨.start,false⟩],block [
  .declare .n (.lit 0), .declare .count (.lit 0),
  .whileLoop (.binary .lt (.var .n) (.var .start)) (block [
    .update (.increment .n),
    .assign .count (.binary .add (.var .count) (.call1 .isPrime (.var .n)))]),
  .returnValue (.var .count)]⟩

def selectedProgram : Program := ⟨64,[primeFunction,countFunction]⟩
def actualSource : String := include_str "../c/verified_primecount.c"

/-- The actual executable C tokens agree with this structural AST, including
both source bodies. This proves a restricted lexical correspondence; it does
not claim a verified unrestricted C compiler or frontend. -/
theorem actual_source_checked :
    LCMSourcePV.RestrictedC.SourceCorresponds render actualSource selectedProgram := by
  refine ⟨(render selectedProgram).getD "",?_,?_,?_⟩
  · simp [render,selectedProgram]
  · decide +kernel
  · decide +kernel

#print axioms actual_source_checked
end RamanujanPV.Source
