/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddArrays
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

structure Input where
  layout : Layout
  old : Nat → Nat → Nat
  subtract : Nat
  subtract_bound : subtract ≤ 1
  digitsA : ∀j < 5,old (layout.object .a) (layout.start .a+j) < base
  digitsB : ∀j < 5,old (layout.object .b) (layout.start .b+j) < base
  signA : old (layout.object .a) (layout.start .a+5) ≤ 1
  signB : old (layout.object .b) (layout.start .b+5) ≤ 1

def Input.a (i : Input) (j : Nat) : Nat:=i.old (i.layout.object .a) (i.layout.start .a+j)
def Input.b (i : Input) (j : Nat) : Nat:=i.old (i.layout.object .b) (i.layout.start .b+j)
def Input.asign (i : Input) : Nat:=i.old (i.layout.object .a) (i.layout.start .a+5)
def Input.bsign (i : Input) : Nat:=if 0 < i.subtract then 1-i.old (i.layout.object .b) (i.layout.start .b+5)
  else i.old (i.layout.object .b) (i.layout.start .b+5)
def Input.cmp (i : Input) : Nat:=compareDigits i.a i.b 5
def Input.left (i : Input) (swap : Bool) : Nat → Nat:=if swap then i.b else i.a
def Input.right (i : Input) (swap : Bool) : Nat → Nat:=if swap then i.a else i.b

theorem Input.left_bound (i : Input) (swap : Bool) : ∀j < 5,i.left swap j < base := by
  cases swap with
  | false=>exact i.digitsA
  | true=>exact i.digitsB
theorem Input.right_bound (i : Input) (swap : Bool) : ∀j < 5,i.right swap j < base := by
  cases swap with
  | false=>exact i.digitsB
  | true=>exact i.digitsA

inductive Var where | out | a | b | subtract | asign | bsign | j | carry | cmp deriving DecidableEq
def name : Var → String
  | .out=>"out" | .a=>"a" | .b=>"b" | .subtract=>"subtract" | .asign=>"as" | .bsign=>"bs"
  | .j=>"j" | .carry=>"carry" | .cmp=>"cmp"
def type : Var → CType | .out | .a | .b=>.pointer .u64 | _=>.u64
def values (i : Input) (j carry : Nat) : Var → Value
  | .out=>.pointer (wordPointer (i.layout.object .out) (i.layout.start .out))
  | .a=>.pointer (wordPointer (i.layout.object .a) (i.layout.start .a))
  | .b=>.pointer (wordPointer (i.layout.object .b) (i.layout.start .b))
  | .subtract=>.integer (integer64 i.subtract)
  | .asign=>.integer (integer64 i.asign)
  | .bsign=>.integer (integer64 i.bsign)
  | .j=>.integer (integer64 j)
  | .carry=>.integer (integer64 carry)
  | .cmp=>.integer (integer64 i.cmp)

def condition : Expr:=.binary .lt (.variable "j") (.literal (.integer 5 "ULL"))
def addTExpr : Expr:=.paren (.binary .add
  (.paren (.binary .add (.index (.variable "a") (.variable "j")) (.index (.variable "b") (.variable "j"))))
  (.variable "carry"))
def subTExpr : Expr:=.paren (.binary .sub
  (.paren (.binary .sub (.paren (.binary .add (.literal (.integer 1000000000 "ULL")) (.variable "left")))
    (.variable "right"))) (.variable "carry"))
def digitStmt : Stmt:=.assign (.index (.variable "out") (.variable "j"))
  (.paren (.binary .mod (.variable "t") (.literal (.integer 1000000000 "ULL"))))
def carryExpr (sub : Bool) : Expr:=if sub then .paren (.binary .sub (.literal (.integer 1 "ULL"))
  (.paren (.binary .div (.variable "t") (.literal (.integer 1000000000 "ULL")))))
  else .paren (.binary .div (.variable "t") (.literal (.integer 1000000000 "ULL")))
def carryStmt (sub : Bool) : Stmt:=.assign (.variable "carry") (carryExpr sub)
def advanceStmt : Stmt:=.assign (.variable "j") (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL"))))
def addLoopBody : Stmt:=.block [.declare .u64 "t" (some addTExpr),digitStmt,carryStmt false,advanceStmt]
def addLoop : Stmt:=.whileLoop condition addLoopBody

structure View {F : Type} (state : State F) (input : Input) (sub swap : Bool)
    (owner : Nat) (li : Var → Nat) (j : Nat) : Prop where
  arrays : Arrays state input.layout input.old sub (input.left swap) (input.right swap) j
  locals : Locals state name type li owner (values input j (scan sub (input.left swap) (input.right swap) j).2)
  separate : ∀r v,input.layout.object r≠li v
  active : j ≤ 5
  well : WellScoped state

theorem View.enter {F : Type} {state : State F} {input : Input} {sub swap : Bool}
    {owner j : Nat} {li : Var → Nat} (h : View state input sub swap owner li j) :
    View state.enterScope input sub swap owner li j :=
  ⟨h.arrays.enter,h.locals.enter,h.separate,h.active,wellScoped_enter h.well⟩

theorem View.carry_bound {F : Type} {state : State F} {input : Input} {sub swap : Bool}
    {owner j : Nat} {li : Var → Nat} (h : View state input sub swap owner li j) :
    (scan sub (input.left swap) (input.right swap) j).2 ≤ 1 :=
  (scan_bounds sub _ _ j (fun k hk=>input.left_bound swap k (lt_of_lt_of_le hk h.active))
    (fun k hk=>input.right_bound swap k (lt_of_lt_of_le hk h.active))).1

theorem condition_eval {F : Type} (context : Context F) {state : State F} {input : Input} {sub swap : Bool}
    {owner j : Nat} {li : Var → Nat} (h : View state input sub swap owner li j) :
    Eval context state condition (.integer (.boolean (decide (j < 5)))) state :=
  .binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
    (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
    (by simp only [values,binary,CompareSource.binary64_lt j 5 (by have hj:=h.active; omega) (by norm_num),Option.map_some])

theorem left_eval {F : Type} (context : Context F) {state : State F} {input : Input} {sub swap : Bool}
    {owner j : Nat} {li : Var → Nat} (h : View state input sub swap owner li j) (hj : j < 5) :
    Eval context state (.index (.variable "a") (.variable "j")) (.integer (integer64 (input.a j))) state :=
  source_index_eval context h.arrays .a (by decide) _ _
    (.variable (h.locals.lookup Var.a) (h.locals.read Var.a))
    (.variable (h.locals.lookup Var.j) (h.locals.read Var.j)) hj

theorem right_eval {F : Type} (context : Context F) {state : State F} {input : Input} {sub swap : Bool}
    {owner j : Nat} {li : Var → Nat} (h : View state input sub swap owner li j) (hj : j < 5) :
    Eval context state (.index (.variable "b") (.variable "j")) (.integer (integer64 (input.b j))) state :=
  source_index_eval context h.arrays .b (by decide) _ _
    (.variable (h.locals.lookup Var.b) (h.locals.read Var.b))
    (.variable (h.locals.lookup Var.j) (h.locals.read Var.j)) hj

#print axioms condition_eval
#print axioms left_eval
#print axioms right_eval
end RH080Next.FFTPV.AddSource
