/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTNormalizeProfiles
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AnswerSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

def sentinel : Nat:=18446744073709551615
def limit : Nat:=18446744073709551000

def computed (first second prior allowance : Nat) : Nat:=
  if first<limit then if second<limit-first then first+second+allowance else prior else prior

def firstTest : Expr:=.binary .lt (.variable "first") (.literal (.integer limit "ULL"))
def secondTest : Expr:=.binary .lt (.variable "second") (.paren (.binary .sub (.literal (.integer limit "ULL")) (.variable "first")))
def assignment (allowance : Nat) : Stmt:=.assign (.variable "answer")
  (.paren (.binary .add (.paren (.binary .add (.variable "first") (.variable "second"))) (.literal (.integer allowance "ULL"))))
def innerBranch (allowance : Nat) : Stmt:=.ite secondTest (.block [assignment allowance]) none
def logic (allowance : Nat) : Stmt:=.ite firstTest (.block [innerBranch allowance]) none

def firstDeclaration : Stmt:=.declare .u64 "first" (some (.call "convert_bound" [.variable "total",.literal (.integer 6 "ULL")]))
def secondDeclaration : Stmt:=.declare .u64 "second" (some (.call "convert_bound" [.variable "quad",.literal (.integer 6 "ULL")]))
def statusBranch (allowance : Nat) : Stmt:=.ite (.binary .eq (.variable "status") (.literal (.integer 0 "ULL")))
  (.block [firstDeclaration,secondDeclaration,logic allowance]) none

def answerDeclaration : Stmt:=.declare .u64 "answer" (some (.literal (.integer sentinel "ULL")))

theorem actual_w4_answer : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[39]?=some answerDeclaration:=by rfl
theorem actual_fap_answer : (ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body)[39]?=some answerDeclaration:=by rfl
theorem actual_w4_status : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[40]?=some (statusBranch 100):=by rfl
theorem actual_fap_status : (ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body)[40]?=some (statusBranch 20):=by rfl

inductive Var where | total | quad | status | answer | first | second deriving DecidableEq

def name : Var→String | .total=>"total" | .quad=>"quad" | .status=>"status" | .answer=>"answer" | .first=>"first" | .second=>"second"
def type : Var→CType | .total | .quad=>.pointer .u64 | _=>.u64

def values (workObject first second answer : Nat) : Var→Value
  | .total=>.pointer (wordPointer workObject 192)
  | .quad=>.pointer (wordPointer workObject 208)
  | .status=>.integer (integer64 0)
  | .answer=>.integer (integer64 answer)
  | .first=>.integer (integer64 first)
  | .second=>.integer (integer64 second)

structure View {F : Type} (state : State F) (workObject : Nat) (ids owners : Var→Nat)
    (first second answer : Nat) (data : Nat→Nat) : Prop where
  params : ProductInner.Bindings state name type ids owners (values workObject first second answer)
  array : WordArrayRep state workObject 512 data
  separate : ∀v,workObject≠ids v
  firstFits : first<2^64
  secondFits : second<2^64
  answerFits : answer<2^64
  well : WellScoped state

theorem View.enter {F : Type} {state : State F} {workObject first second answer : Nat}
    {ids owners : Var→Nat} {data : Nat→Nat} (h : View state workObject ids owners first second answer data) :
    View state.enterScope workObject ids owners first second answer data:=
  ⟨h.params.enter,h.array,h.separate,h.firstFits,h.secondFits,h.answerFits,wellScoped_enter h.well⟩

theorem computed_fits (first second prior allowance : Nat) (old : prior<2^64) (budget : allowance≤615) :
    computed first second prior allowance<2^64:=by
  unfold computed
  split
  · rename_i hfirst
    split
    · rename_i hsecond
      dsimp [limit] at *
      omega
    · exact old
  · exact old

theorem first_test {F : Type} (context : Context F) {state : State F} {workObject first second answer : Nat}
    {ids owners : Var→Nat} {data : Nat→Nat} (h : View state workObject ids owners first second answer data) :
    Eval context state firstTest (.integer (.boolean (decide (first<limit)))) state:=
  .binaryLR (.variable (h.params.lookup Var.first) (h.params.read Var.first))
    (.literal (.integer limit "ULL") _ (.integer (integer64 limit)) (by rfl))
    (by simp only [values,binary,binary64_lt first limit h.firstFits (by norm_num [limit]),Option.map_some])

theorem second_test {F : Type} (context : Context F) {state : State F} {workObject first second answer : Nat}
    {ids owners : Var→Nat} {data : Nat→Nat} (h : View state workObject ids owners first second answer data) (inside : first<limit) :
    Eval context state secondTest (.integer (.boolean (decide (second<limit-first)))) state:=by
  have sub : Eval context state (.paren (.binary .sub (.literal (.integer limit "ULL")) (.variable "first")))
      (.integer (integer64 (limit-first))) state:=
    .paren (.binaryLR (.literal (.integer limit "ULL") _ (.integer (integer64 limit)) (by rfl))
      (.variable (h.params.lookup Var.first) (h.params.read Var.first))
      (by simp only [values,binary,binary64_sub limit first (by norm_num [limit]) h.firstFits (Nat.le_of_lt inside),Option.map_some]))
  exact .binaryLR (.variable (h.params.lookup Var.second) (h.params.read Var.second)) sub
    (by simp only [values,binary,binary64_lt second (limit-first) h.secondFits (by dsimp [limit];omega),Option.map_some])

#print axioms actual_w4_status
#print axioms actual_fap_status
#print axioms computed_fits
#print axioms first_test
#print axioms second_test
end RH080Next.FFTPV.AnswerSource
