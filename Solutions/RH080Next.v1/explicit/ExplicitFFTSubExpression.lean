/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddLoop
import FFTWordSubtraction
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def cmpTest : Expr:=.binary .eq (.variable "cmp") (.literal (.integer 0 "ULL"))
def swapBranch : Stmt:=.ite cmpTest (.block [
  .assign (.variable "left") (.index (.variable "b") (.variable "j")),
  .assign (.variable "right") (.index (.variable "a") (.variable "j"))]) none
def subLoopBody : Stmt:=.block [
  .declare .u64 "left" (some (.index (.variable "a") (.variable "j"))),
  .declare .u64 "right" (some (.index (.variable "b") (.variable "j"))),swapBranch,
  .declare .u64 "t" (some subTExpr),digitStmt,carryStmt true,advanceStmt]
def subLoop : Stmt:=.whileLoop condition subLoopBody

theorem cmp_eval {F : Type} (context : Context F) {state : State F} {input : Input} {sub swap : Bool}
    {owner j : Nat} {li : Var → Nat} (h : View state input sub swap owner li j) :
    Eval context state cmpTest (.integer (.boolean (decide (input.cmp=0)))) state := by
  have hc : input.cmp ≤ 2:=CompareSource.compareDigits_le_two _ _ _
  exact .binaryLR (.variable (h.locals.lookup Var.cmp) (h.locals.read Var.cmp))
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by simp only [values,binary,binary64_eq input.cmp 0 (by omega) (by norm_num),Option.map_some])

/-- All three unsigned operations in B+left−right−carry are on their exact
nonunderflow domain; natural subtraction is not a wrapping shortcut. -/
theorem sub_t_eval {F : Type} (context : Context F) {state : State F} {input : Input}
    {swap : Bool} {owner j : Nat} {li : Var → Nat} (h : View state input true swap owner li j) (hj : j < 5)
    (readLeft : Eval context state (.variable "left") (.integer (integer64 (input.left swap j))) state)
    (readRight : Eval context state (.variable "right") (.integer (integer64 (input.right swap j))) state) :
    Eval context state subTExpr (.integer (integer64
      (digitTotal true (input.left swap j) (input.right swap j) (scan true (input.left swap) (input.right swap) j).2))) state := by
  let a:=input.left swap j
  let b:=input.right swap j
  let c:=(scan true (input.left swap) (input.right swap) j).2
  have ha : a < base:=input.left_bound swap j hj
  have hb : b < base:=input.right_bound swap j hj
  have hc : c ≤ 1:=h.carry_bound
  have a64 : a < 2^64:=lt_trans ha (by norm_num [base])
  have b64 : b < 2^64:=lt_trans hb (by norm_num [base])
  have c64 : c < 2^64:=by omega
  have sum64 : base+a < 2^64:=by dsimp [base] at ha ⊢; omega
  have diff64 : base+a-b < 2^64:=lt_of_le_of_lt (Nat.sub_le _ _) sum64
  have sub1 : b ≤ base+a:=by omega
  have sub2 : c ≤ base+a-b:=by omega
  have sum : Eval context state (.paren (.binary .add (.literal (.integer 1000000000 "ULL")) (.variable "left")))
      (.integer (integer64 (base+a))) state:=
    .paren (.binaryLR (.literal (.integer 1000000000 "ULL") _ (.integer (integer64 base)) (by rfl)) readLeft
      (congrArg (Option.map Value.integer) (binary64_add base a (by norm_num [base]) a64 sum64)))
  have difference : Eval context state (.paren (.binary .sub
      (.paren (.binary .add (.literal (.integer 1000000000 "ULL")) (.variable "left"))) (.variable "right")))
      (.integer (integer64 (base+a-b))) state:=
    .paren (.binaryLR sum readRight (congrArg (Option.map Value.integer) (binary64_sub (base+a) b sum64 b64 sub1)))
  exact .paren (.binaryLR difference (.variable (h.locals.lookup Var.carry) (h.locals.read Var.carry))
    (congrArg (Option.map Value.integer) (binary64_sub (base+a-b) c diff64 c64 sub2)))

#print axioms cmp_eval
#print axioms sub_t_eval
end RH080Next.FFTPV.AddSource
