/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootRuntime
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

def twiceIndex : Expr:=.paren (.binary .mul (.literal (.integer 2 "ULL")) (.variable "i"))
def oddIndex : Expr:=.paren (.binary .sub twiceIndex (.literal (.integer 1 "ULL")))
def nextOddIndex : Expr:=.paren (.binary .add twiceIndex (.literal (.integer 1 "ULL")))
def cosineDivisor : Expr:=.paren (.binary .mul twiceIndex oddIndex)
def sineDivisor : Expr:=.paren (.binary .mul twiceIndex nextOddIndex)
def parityIndex : Expr:=.paren (.binary .mod (.variable "i") (.literal (.integer 2 "ULL")))
def loopCondition : Expr:=.binary .le (.variable "i") (.literal (.integer 10 "ULL"))

theorem cosine_divisor_pure : SourcePure.CallFree cosineDivisor:=by
  simp [cosineDivisor,twiceIndex,oddIndex,SourcePure.CallFree]
theorem sine_divisor_pure : SourcePure.CallFree sineDivisor:=by
  simp [sineDivisor,twiceIndex,nextOddIndex,SourcePure.CallFree]
theorem parity_index_pure : SourcePure.CallFree parityIndex:=by simp [parityIndex,SourcePure.CallFree]
theorem loop_condition_pure : SourcePure.CallFree loopCondition:=by simp [loopCondition,SourcePure.CallFree]

theorem twice_index_eval {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner statusId indexId j : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data (j+1)) (hj : j<10) :
    Eval context before twiceIndex (.integer (integer64 (2*(j+1)))) before:=by
  apply Eval.paren
  apply Eval.binaryLR (.literal (.integer 2 "ULL") _ (.integer (integer64 2)) (by rfl))
    (.variable h.lookup h.counter.read)
  change (Integer.binary .mul (integer64 2) (integer64 (j+1))).map _=_
  interval_cases j <;> rfl

theorem odd_index_eval {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner statusId indexId j : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data (j+1)) (hj : j<10) :
    Eval context before oddIndex (.integer (integer64 (2*(j+1)-1))) before:=by
  apply Eval.paren
  apply Eval.binaryLR (twice_index_eval context h hj)
    (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
  change (Integer.binary .sub (integer64 (2*(j+1))) (integer64 1)).map _=_
  interval_cases j <;> rfl

theorem next_odd_index_eval {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner statusId indexId j : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data (j+1)) (hj : j<10) :
    Eval context before nextOddIndex (.integer (integer64 (2*(j+1)+1))) before:=by
  apply Eval.paren
  apply Eval.binaryLR (twice_index_eval context h hj)
    (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
  change (Integer.binary .add (integer64 (2*(j+1))) (integer64 1)).map _=_
  interval_cases j <;> rfl

theorem cosine_divisor_eval {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner statusId indexId j : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data (j+1)) (hj : j<10) :
    Eval context before cosineDivisor (.integer (integer64 (2*(j+1)*(2*(j+1)-1)))) before:=by
  apply Eval.paren
  apply Eval.binaryLR (twice_index_eval context h hj) (odd_index_eval context h hj)
  change (Integer.binary .mul (integer64 (2*(j+1))) (integer64 (2*(j+1)-1))).map _=_
  interval_cases j <;> rfl

theorem sine_divisor_eval {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner statusId indexId j : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data (j+1)) (hj : j<10) :
    Eval context before sineDivisor (.integer (integer64 (2*(j+1)*(2*(j+1)+1)))) before:=by
  apply Eval.paren
  apply Eval.binaryLR (twice_index_eval context h hj) (next_odd_index_eval context h hj)
  change (Integer.binary .mul (integer64 (2*(j+1))) (integer64 (2*(j+1)+1))).map _=_
  interval_cases j <;> rfl

theorem parity_index_eval {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner statusId indexId j : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data (j+1)) (hj : j<10) :
    Eval context before parityIndex (.integer (integer64 ((j+1)%2))) before:=by
  apply Eval.paren
  apply Eval.binaryLR (.variable h.lookup h.counter.read)
    (.literal (.integer 2 "ULL") _ (.integer (integer64 2)) (by rfl))
  change (Integer.binary .mod (integer64 (j+1)) (integer64 2)).map _=_
  interval_cases j <;> rfl

theorem loop_condition_eval {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner statusId indexId j : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data (j+1)) (hj : j≤10) :
    Eval context before loopCondition (.integer (.boolean (decide (j<10)))) before:=by
  apply Eval.binaryLR (.variable h.lookup h.counter.read)
    (.literal (.integer 10 "ULL") _ (.integer (integer64 10)) (by rfl))
  change (Integer.binary .le (integer64 (j+1)) (integer64 10)).map _=_
  interval_cases j <;> rfl

def iterationStatements : List Stmt:=[
  multiplyStatement .work 24 .work 12 .work 6,
  copySliceStatement .work 12 .work 24,
  floorDivideStatement .work 12 cosineDivisor,
  multiplyStatement .work 24 .work 18 .work 6,
  copySliceStatement .work 18 .work 24,
  floorDivideStatement .work 18 sineDivisor,
  addStatement .root 0 .work 12 parityIndex,
  addStatement .root 6 .work 18 parityIndex,indexIncrement]

def sourceLoop : Stmt:=.whileLoop loopCondition (.block iterationStatements)
def finalSignStatement : Stmt:=literalStore .root 11 1
def finalCanonicalStatement : Stmt:=.expression (.call "canonical_sign" [pointerExpr .root 6])
def returnStatusStatement : Stmt:=.returnValue (some (.variable "status"))
def sourceStatements : List Stmt:=xPrefixStatements++squareStatement::setupStatements++
  [indexDeclaration,sourceLoop,finalSignStatement,finalCanonicalStatement,returnStatusStatement]

/-- All nineteen unchanged initializer source statements, with the exact
parentheses and source ordering consumed by the actual AST. -/
theorem actual_source_statements : initialize_root_ast.body=.block sourceStatements:=by rfl

#print axioms cosine_divisor_eval
#print axioms sine_divisor_eval
#print axioms parity_index_eval
#print axioms loop_condition_eval
#print axioms actual_source_statements
end RH080Next.FFTPV.RootSource
