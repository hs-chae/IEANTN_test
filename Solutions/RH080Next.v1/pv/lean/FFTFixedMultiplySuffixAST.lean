/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveAST
set_option autoImplicit false
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect

def lit (n : Nat) : Expr := .literal (.integer n "ULL")
def v (s : String) : Expr := .variable s
def signDeclaration : Stmt := .declare .u64 "sign" (some (lit 0))
def signCondition : Expr := .binary .ne (.index (v "a") (lit 5)) (.index (v "b") (lit 5))
def signBranch : Stmt := .ite signCondition (.block [.assign (v "sign") (lit 1)]) none
def lostDeclaration : Stmt := .declare .u64 "lost" (some (lit 0))
def resetIndex : Stmt := .assign (v "i") (lit 0)
def increment : Stmt := .assign (v "i") (.paren (.binary .add (v "i") (lit 1)))
def lostExpression : Expr := .paren (.binary .add (v "lost") (.index (v "work") (v "i")))
def lostStore : Stmt := .assign (v "lost") lostExpression
def lostCondition : Expr := .binary .lt (v "i") (lit 4)
def lostBody : Stmt := .block [lostStore, increment]
def lostLoop : Stmt := .whileLoop lostCondition lostBody
def copyStore : Stmt := .assign (.index (v "out") (v "i"))
  (.index (v "work") (.paren (.binary .add (v "i") (lit 4))))
def copyCondition : Expr := .binary .lt (v "i") (lit 5)
def copyBody : Stmt := .block [copyStore, increment]
def copyLoop : Stmt := .whileLoop copyCondition copyBody
def signStore : Stmt := .assign (.index (v "out") (lit 5)) (v "sign")
def overflowDeclaration : Stmt := .declare .u64 "overflow" (some (.index (v "work") (lit 9)))
def roundCondition : Expr := .binary .gt (v "sign") (lit 0)
def lostPositive : Expr := .binary .gt (v "lost") (lit 0)
def incrementCall : Expr := .call "increment_words" [v "out", lit 5]
def incrementOverflow : Stmt := .assign (v "overflow") (.paren (.binary .add (v "overflow") incrementCall))
def roundingBranch : Stmt := .ite roundCondition
  (.block [.ite lostPositive (.block [incrementOverflow]) none]) none
def canonicalCall : Stmt := .expression (.call "canonical_sign" [v "out"])
def returnOverflow : Stmt := .returnValue (some (v "overflow"))
def statements : List Stmt := [signDeclaration, signBranch, lostDeclaration, resetIndex,
  lostLoop, resetIndex, copyLoop, signStore, overflowDeclaration, roundingBranch,
  canonicalCall, returnOverflow]

/-- Exact remaining source instructions after the verified zero/i/core prefix. -/
theorem actual_suffix : (match FFTRecursivePV.fixed_multiply_ast.body with
    | .block body => body.drop 3 | _ => []) = statements := by rfl

#print axioms actual_suffix
end RH080Next.FFTPV.MultiplySuffix
