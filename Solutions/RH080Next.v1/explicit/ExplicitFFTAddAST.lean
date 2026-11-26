/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTSubLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

def asDeclaration : Stmt:=.declare .u64 "as" (some (.index (.variable "a") (.literal (.integer 5 "ULL"))))
def bsDeclaration : Stmt:=.declare .u64 "bs" (some (.index (.variable "b") (.literal (.integer 5 "ULL"))))
def flipTest : Expr:=.binary .gt (.variable "subtract") (.literal (.integer 0 "ULL"))
def flipSign : Stmt:=.assign (.variable "bs") (.paren (.binary .sub (.literal (.integer 1 "ULL")) (.variable "bs")))
def flipBranch : Stmt:=.ite flipTest (.block [flipSign]) none
def jDeclaration : Stmt:=.declare .u64 "j" (some (.literal (.integer 0 "ULL")))
def carryDeclaration : Stmt:=.declare .u64 "carry" (some (.literal (.integer 0 "ULL")))
def cmpDeclaration : Stmt:=.declare .u64 "cmp" (some (.call "magnitude_compare" [.variable "a",.variable "b"]))
def sameSignTest : Expr:=.binary .eq (.variable "as") (.variable "bs")
def storeSign (cname : String) : Stmt:=.assign (.index (.variable "out") (.literal (.integer 5 "ULL"))) (.variable cname)
def additionBranch : Stmt:=.block [addLoop,storeSign "as"]
def signDeclaration : Stmt:=.declare .u64 "sign" (some (.variable "as"))
def chooseSign : Stmt:=.ite cmpTest (.block [.assign (.variable "sign") (.variable "bs")]) none
def clearCarry : Stmt:=.assign (.variable "carry") (.literal (.integer 0 "ULL"))
def subtractionBranch : Stmt:=.block [signDeclaration,chooseSign,subLoop,storeSign "sign",clearCarry]
def arithmeticBranch : Stmt:=.ite sameSignTest additionBranch (some subtractionBranch)
def canonicalStatement : Stmt:=.expression (.call "canonical_sign" [.variable "out"])
def returnStatement : Stmt:=.returnValue (some (.variable "carry"))
def functionStatements : List Stmt:=[asDeclaration,bsDeclaration,flipBranch,jDeclaration,carryDeclaration,
  cmpDeclaration,arithmeticBranch,canonicalStatement,returnStatement]

/-- Every source statement being refined is literally the independently
parsed original fixed_add AST; no replacement numerical program is used. -/
theorem actual_body : fixed_add_ast.body=.block functionStatements:=by rfl

#print axioms actual_body
end RH080Next.FFTPV.AddSource
