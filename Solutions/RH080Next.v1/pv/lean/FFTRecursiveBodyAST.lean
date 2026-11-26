/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLeafExpressions
import FFTStatusCall
set_option autoImplicit false
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect

def literal (n : Nat) : Expr := .literal (.integer n "ULL")
def addExpr (a b : Expr) : Expr := .paren (.binary .add a b)
def mulExpr (a b : Expr) : Expr := .paren (.binary .mul a b)
def pointerOffset (name : String) (n : Nat) : Expr := addExpr (.variable name) (literal n)

def recursiveArguments (right : Bool) : List Expr :=
  [.variable "output",if right then addExpr (.variable "start") (.variable "half") else .variable "start",
   .variable "input",if right then addExpr (.variable "index") (.variable "step") else .variable "index",
   mulExpr (.variable "step") (literal 2),.variable "twiddle",.variable "half",.variable "total",.variable "work"]

def halfDeclaration : Stmt :=
  .declare .u64 "half" (some (.paren (.binary .div (.variable "n") (literal 2))))
def statusDeclaration : Stmt :=
  .declare .u64 "status" (some (.call "fft_recursive" (recursiveArguments false)))
def rightRecursiveCall : Stmt := StatusCall.statement "fft_recursive" (recursiveArguments true)
def strideDeclaration : Stmt :=
  .declare .u64 "stride" (some (.paren (.binary .div (.variable "total") (.variable "n"))))
def jDeclaration : Stmt := .declare .u64 "j" (some (literal 0))
def tempDeclaration : Stmt := .declare (.pointer .u64) "temp" (some (pointerOffset "work" 160))

def butterflyA : Expr := addExpr (.variable "output")
  (mulExpr (addExpr (.variable "start") (.variable "j")) (literal 12))
def butterflyB : Expr := addExpr (.variable "output")
  (mulExpr (addExpr (addExpr (.variable "start") (.variable "j")) (.variable "half")) (literal 12))
def butterflyW : Expr := addExpr (.variable "twiddle")
  (mulExpr (mulExpr (.variable "j") (.variable "stride")) (literal 12))

def butterflyArguments (which : Fin 5) : List Expr :=
  match which.val with
  | 0 => [.variable "temp",.variable "b",.variable "w",.variable "work"]
  | 1 => [pointerOffset "work" 48,.variable "a",.variable "temp",literal 0]
  | 2 => [pointerOffset "work" 54,pointerOffset "a" 6,pointerOffset "temp" 6,literal 0]
  | 3 => [.variable "b",.variable "a",.variable "temp",literal 1]
  | _ => [pointerOffset "b" 6,pointerOffset "a" 6,pointerOffset "temp" 6,literal 1]

def butterflyCopy : Stmt := .expression (.call "copy_words"
  [.variable "a",pointerOffset "work" 48,literal 12])
def incrementJ : Stmt := .assign (.variable "j") (addExpr (.variable "j") (literal 1))
def butterflyStatements : List Stmt :=
  [.declare (.pointer .u64) "a" (some butterflyA),
   .declare (.pointer .u64) "b" (some butterflyB),
   .declare (.pointer .u64) "w" (some butterflyW),
   StatusCall.statement "complex_multiply" (butterflyArguments 0),
   StatusCall.statement "fixed_add" (butterflyArguments 1),
   StatusCall.statement "fixed_add" (butterflyArguments 2),
   StatusCall.statement "fixed_add" (butterflyArguments 3),
   StatusCall.statement "fixed_add" (butterflyArguments 4),butterflyCopy,incrementJ]

def loopCondition : Expr := .binary .lt (.variable "j") (.variable "half")
def butterflyLoop : Stmt := .whileLoop loopCondition (.block butterflyStatements)
def finalReturn : Stmt := .returnValue (some (.variable "status"))

/-- Every statement and parenthesis here is definitionally the unchanged source
AST. The independently checked source grammar is consumed by the final wrapper. -/
theorem actual_function_decomposition : functionStatements =
    [leafBranch,halfDeclaration,statusDeclaration,rightRecursiveCall,strideDeclaration,
      jDeclaration,tempDeclaration,butterflyLoop,finalReturn] := by rfl

#print axioms actual_function_decomposition
end RH080Next.FFTPV.RecursiveSource
