/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexSourceFinal
import FFTWordDivision
import GoldbachDirect.SourceArrayFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ConvertBoundSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

def base : Nat:=1000000000
def sentinel : Nat:=18446744073709551615

def allZero (data : Nat→Nat) (start : Nat) : Nat→Nat→Bool
  | 0,_=>true
  | steps+1,i=>decide (data (start+i)=0) && allZero data start steps (i+1)

def lower (data : Nat→Nat) (start : Nat) : Nat:=data start+base*data (start+1)
def result (data : Nat→Nat) (start : Nat) : Nat:=if allZero data start 4 2 then lower data start else sentinel

def declaration : Stmt:=.declare .u64 "i" (some (.literal (.integer 2 "ULL")))
def condition : Expr:=.binary .lt (.variable "i") (.variable "n")
def test : Expr:=.binary .ne (.index (.variable "a") (.variable "i")) (.literal (.integer 0 "ULL"))
def returnSentinel : Stmt:=.returnValue (some (.literal (.integer sentinel "ULL")))
def branch : Stmt:=.ite test (.block [returnSentinel]) none
def advance : Stmt:=.assign (.variable "i") (.paren (.binary .add (.variable "i") (.literal (.integer 1 "ULL"))))
def loopBody : Stmt:=.block [branch,advance]
def loop : Stmt:=.whileLoop condition loopBody
def returnLower : Stmt:=.returnValue (some (.paren (.binary .add (.index (.variable "a") (.literal (.integer 0 "ULL")))
  (.paren (.binary .mul (.literal (.integer base "ULL")) (.index (.variable "a") (.literal (.integer 1 "ULL"))))))))
def statements : List Stmt:=[declaration,loop,returnLower]

theorem actual_body : convert_bound_ast.body=.block statements:=by rfl

inductive Var where | a | n | i deriving DecidableEq

def name : Var→String | .a=>"a" | .n=>"n" | .i=>"i"
def type : Var→CType | .a=>.pointer .u64 | _=>.u64

def values (object start i : Nat) : Var→Value
  | .a=>.pointer (wordPointer object start)
  | .n=>.integer (integer64 6)
  | .i=>.integer (integer64 i)

structure View {F : Type} (state : State F) (object size start : Nat)
    (ids : Var→Nat) (owner : Nat) (data : Nat→Nat) (i : Nat) : Prop where
  array : WordArrayRep state object size data
  locals : Locals state name type ids owner (values object start i)
  separate : ∀v,object≠ids v
  bound : start+6≤size
  digits : ∀k,k<6 →data (start+k)<base
  active : i≤6
  well : WellScoped state

theorem View.enter {F : Type} {state : State F} {object size start owner i : Nat}
    {ids : Var→Nat} {data : Nat→Nat} (h : View state object size start ids owner data i) :
    View state.enterScope object size start ids owner data i:=
  ⟨h.array,h.locals.enter,h.separate,h.bound,h.digits,h.active,wellScoped_enter h.well⟩

theorem condition_eval {F : Type} (context : Context F) {state : State F} {object size start owner i : Nat}
    {ids : Var→Nat} {data : Nat→Nat} (h : View state object size start ids owner data i) :
    Eval context state condition (.integer (.boolean (decide (i<6)))) state:=by
  exact .binaryLR (.variable (h.locals.lookup Var.i) (h.locals.read Var.i))
    (.variable (h.locals.lookup Var.n) (h.locals.read Var.n))
    (by simp only [values,binary,binary64_lt i 6 (by have hi:=h.active;omega) (by norm_num),Option.map_some])

theorem index_eval {F : Type} (context : Context F) {state : State F} {object size start owner i : Nat}
    {ids : Var→Nat} {data : Nat→Nat} (h : View state object size start ids owner data i) (hi : i<6) :
    Eval context state (.index (.variable "a") (.variable "i")) (.integer (integer64 (data (start+i)))) state:=by
  exact .load (.index (.variable (h.locals.lookup Var.a) (h.locals.read Var.a))
    (.variable (h.locals.lookup Var.i) (h.locals.read Var.i)) (slice_pointer_add h.array (by have hb:=h.bound;omega)))
    (word_load h.array (by have hb:=h.bound;omega))

theorem binary64_ne (a b : Nat) (ha : a<2^64) (hb : b<2^64) :
    Integer.binary .ne (integer64 a) (integer64 b)=some (.boolean (decide (a≠b))):=by
  change some (Integer.boolean ((Integer.cast .u64 (a:Int)).toInt != (Integer.cast .u64 (b:Int)).toInt))=_
  rw [cast64_exact a ha,cast64_exact b hb,integer64_toInt,integer64_toInt]
  congr 2
  by_cases he : a=b
  · subst b; simp
  · have hc : (a:Int)≠(b:Int) := by exact_mod_cast he
    simp [bne,he,hc]

theorem test_eval {F : Type} (context : Context F) {state : State F} {object size start owner i : Nat}
    {ids : Var→Nat} {data : Nat→Nat} (h : View state object size start ids owner data i) (hi : i<6) :
    Eval context state test (.integer (.boolean (decide (data (start+i)≠0)))) state:=by
  exact .binaryLR (index_eval context h hi)
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by
      have hn := binary64_ne (data (start+i)) 0 (by have hd:=h.digits i hi;dsimp [base] at hd;omega) (by norm_num)
      simp only [binary,hn,Option.map_some])

#print axioms actual_body
#print axioms condition_eval
#print axioms test_eval
end RH080Next.FFTPV.ConvertBoundSource
