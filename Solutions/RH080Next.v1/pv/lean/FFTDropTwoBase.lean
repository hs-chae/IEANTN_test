/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DropTwoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

inductive Var where | total | i | lost | status deriving DecidableEq

def name : Var→String | .total=>"total" | .i=>"i" | .lost=>"lost" | .status=>"status"
def type : Var→CType | .total=>.pointer .u64 | _=>.u64

def values (workObject : Nat) (old : Nat→Nat) (i : Nat) : Var→Value
  | .total=>.pointer (wordPointer workObject 192)
  | .i=>.integer (integer64 i)
  | .lost=>.integer (integer64 (lost old 192))
  | .status=>.integer (integer64 0)

def condition : Expr:=.binary .lt (.variable "i") (.literal (.integer 4 "ULL"))
def sourceIndex : Expr:=.paren (.binary .add (.variable "i") (.literal (.integer 2 "ULL")))
def move : Stmt:=.assign (.index (.variable "total") (.variable "i")) (.index (.variable "total") sourceIndex)
def advance : Stmt:=.assign (.variable "i") (.paren (.binary .add (.variable "i") (.literal (.integer 1 "ULL"))))
def loopBody : Stmt:=.block [move,advance]
def loop : Stmt:=.whileLoop condition loopBody

theorem actual_w4_loop : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[28]?=some loop:=by rfl
theorem actual_fap_loop : (ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body)[28]?=some loop:=by rfl

structure View {F : Type} (state : State F) (workObject : Nat) (ids : Var→Nat) (owner i : Nat) (old : Nat→Nat) : Prop where
  locals : Locals state name type ids owner (values workObject old i)
  array : WordArrayRep state workObject 512 (shifted old 192 i)
  separate : ∀v,workObject≠ids v
  digits : ∀k,k<6 → old (192+k)<base
  active : i≤4
  well : WellScoped state

theorem View.enter {F : Type} {state : State F} {workObject owner i : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (h : View state workObject ids owner i old) : View state.enterScope workObject ids owner i old:=
  ⟨h.locals.enter,h.array,h.separate,h.digits,h.active,wellScoped_enter h.well⟩

theorem condition_eval {F : Type} (context : Context F) {state : State F} {workObject owner i : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (h : View state workObject ids owner i old) : Eval context state condition (.integer (.boolean (decide (i<4)))) state:=by
  exact .binaryLR (.variable (h.locals.lookup Var.i) (h.locals.read Var.i))
    (.literal (.integer 4 "ULL") _ (.integer (integer64 4)) (by rfl))
    (by simp only [values,binary,binary64_lt i 4 (by have a:=h.active;omega) (by norm_num),Option.map_some])

theorem source_eval {F : Type} (context : Context F) {state : State F} {workObject owner i : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (h : View state workObject ids owner i old) (inside : i<4) :
    Eval context state (.index (.variable "total") sourceIndex) (.integer (integer64 (old (192+i+2)))) state := by
  have index : Eval context state sourceIndex (.integer (integer64 (i+2))) state:=
    .paren (.binaryLR (.variable (h.locals.lookup Var.i) (h.locals.read Var.i))
      (.literal (.integer 2 "ULL") _ (.integer (integer64 2)) (by rfl))
      (by simp only [values,binary,binary64_add i 2 (by omega) (by norm_num) (by omega),Option.map_some]))
  apply Eval.load (.index (.variable (h.locals.lookup Var.total) (h.locals.read Var.total)) index (slice_pointer_add h.array (by omega)))
  simpa only [Nat.add_assoc,shifted_unread old 192 i (192+(i+2)) (Or.inr (by omega))] using word_load h.array (show 192+(i+2)<512 by omega)

#print axioms actual_w4_loop
#print axioms actual_fap_loop
#print axioms condition_eval
#print axioms source_eval
end RH080Next.FFTPV.DropTwoSource
