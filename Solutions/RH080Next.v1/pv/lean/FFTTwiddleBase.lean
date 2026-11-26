/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexSourceFinal
import FFTWordDivision
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.TwiddleSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

inductive Var where | n | twiddle | root | work | status | j deriving DecidableEq

def name : Var→String | .n=>"n" | .twiddle=>"twiddle" | .root=>"root" | .work=>"work" | .status=>"status" | .j=>"j"
def type : Var→CType | .twiddle | .root | .work=>.pointer .u64 | _=>.u64

def values (tableObject workObject n j : Nat) : Var→Value
  | .n=>.integer (integer64 n)
  | .twiddle=>.pointer (wordPointer tableObject 0)
  | .root=>.pointer (wordPointer workObject 128)
  | .work=>.pointer (wordPointer workObject 0)
  | .status=>.integer (integer64 0)
  | .j=>.integer (integer64 j)

def arguments : List Expr := [
  .paren (.binary .add (.variable "twiddle") (.paren (.binary .mul (.variable "j") (.literal (.integer 12 "ULL"))))),
  .paren (.binary .add (.variable "twiddle") (.paren (.binary .mul (.paren (.binary .sub (.variable "j") (.literal (.integer 1 "ULL")))) (.literal (.integer 12 "ULL"))))),
  .variable "root",.variable "work"]
def callStmt : Stmt := StatusCall.statement "complex_multiply" arguments
def advance : Stmt := .assign (.variable "j") (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL"))))
def loopBody : Stmt := .block [callStmt,advance]
def condition : Expr := .binary .lt (.variable "j") (.paren (.binary .div (.variable "n") (.literal (.integer 2 "ULL"))))
def loop : Stmt := .whileLoop condition loopBody

theorem actual_w4_loop : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[19]?=some loop := by rfl
theorem actual_fap_loop : (ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body)[19]?=some loop := by rfl

def sequence (seed : FFT.IntegerModel.CInt) : Nat→FFT.IntegerModel.CInt
  | 0=>(10^36,0)
  | k+1=>FFT.IntegerModel.mul (sequence seed k) seed

structure View {F : Type} (state : State F) (tableObject workObject n : Nat)
    (ids : Var→Nat) (owner j : Nat) (tableData workData : Nat→Nat) (seed : FFT.IntegerModel.CInt) : Prop where
  locals : Locals state name type ids owner (values tableObject workObject n j)
  table : WordArrayRep state tableObject (n/2*12) tableData
  work : WordArrayRep state workObject 512 workData
  different : tableObject≠workObject
  separate : ∀v,tableObject≠ids v ∧ workObject≠ids v
  nbound : 2≤n ∧ n≤16777216
  active : 1≤j ∧ j≤n/2
  tableDigits : ∀k,k<j → ∀c : Fin 2,∀d,d<5 → tableData (k*12+6*c.val+d)<1000000000
  tableSigns : ∀k,k<j → ∀c : Fin 2,tableData (k*12+6*c.val+5)≤1
  tableValues : ∀k,k<j → ComplexSource.pair tableData (k*12)=sequence seed k
  rootDigits : ∀c : Fin 2,∀d,d<5 → workData (128+6*c.val+d)<1000000000
  rootSigns : ∀c : Fin 2,workData (128+6*c.val+5)≤1
  rootValue : ComplexSource.pair workData 128=seed
  rootSmall : seed.1.natAbs≤1000*10^36 ∧ seed.2.natAbs≤1000*10^36
  valuesSmall : ∀k,k<n/2 → (sequence seed k).1.natAbs≤1000*10^36 ∧ (sequence seed k).2.natAbs≤1000*10^36
  well : WellScoped state

theorem View.enter {F : Type} {state : State F} {tableObject workObject n owner j : Nat}
    {ids : Var→Nat} {tableData workData : Nat→Nat} {seed : FFT.IntegerModel.CInt}
    (h : View state tableObject workObject n ids owner j tableData workData seed) :
    View state.enterScope tableObject workObject n ids owner j tableData workData seed :=
  ⟨h.locals.enter,h.table,h.work,h.different,h.separate,h.nbound,h.active,h.tableDigits,h.tableSigns,h.tableValues,
    h.rootDigits,h.rootSigns,h.rootValue,h.rootSmall,h.valuesSmall,wellScoped_enter h.well⟩

section Evaluation
variable {F : Type} (context : Context F) {state : State F} {tableObject workObject n owner j : Nat}
  {ids : Var→Nat} {tableData workData : Nat→Nat} {seed : FFT.IntegerModel.CInt}
  (h : View state tableObject workObject n ids owner j tableData workData seed)
include h

theorem condition_eval : Eval context state condition (.integer (.boolean (decide (j<n/2)))) state := by
  have hn : n<2^64 := by have b:=h.nbound;omega
  have hj : j<2^64 := by have a:=h.active;have b:=h.nbound;omega
  have divEval : Eval context state (.paren (.binary .div (.variable "n") (.literal (.integer 2 "ULL"))))
      (.integer (integer64 (n/2))) state := .paren (.binaryLR (.variable (h.locals.lookup Var.n) (h.locals.read Var.n))
      (.literal (.integer 2 "ULL") _ (.integer (integer64 2)) (by rfl))
      (by simp only [values,binary,binary64_div n 2 hn (by norm_num) (by norm_num),Option.map_some]))
  exact .binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j)) divEval
    (by simp only [values,binary,binary64_lt j (n/2) hj (by omega),Option.map_some])

theorem offset_eval (previous : Bool) :
    Eval context state (if previous then
      Expr.paren (.binary .mul (.paren (.binary .sub (.variable "j") (.literal (.integer 1 "ULL")))) (.literal (.integer 12 "ULL")))
      else .paren (.binary .mul (.variable "j") (.literal (.integer 12 "ULL"))))
      (.integer (integer64 ((if previous then j-1 else j)*12))) state := by
  have hj : j<2^64 := by have a:=h.active;have b:=h.nbound;omega
  have hm : j*12<2^64 := by have a:=h.active;have b:=h.nbound;omega
  cases previous with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    exact .paren (.binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
      (.literal (.integer 12 "ULL") _ (.integer (integer64 12)) (by rfl))
      (by simp only [values,binary,binary64_mul j 12 hj (by norm_num) hm,Option.map_some]))
  | true =>
    simp only [ite_true]
    have sub : Eval context state (.paren (.binary .sub (.variable "j") (.literal (.integer 1 "ULL"))))
      (.integer (integer64 (j-1))) state := .paren (.binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [values,binary,binary64_sub j 1 hj (by norm_num) h.active.1,Option.map_some]))
    have prod := binary64_mul (j-1) 12 (by omega) (by norm_num) (by omega)
    exact .paren (.binaryLR sub (.literal (.integer 12 "ULL") _ (.integer (integer64 12)) (by rfl))
      (by simp only [binary,prod,Option.map_some]))

theorem arguments_eval (inside : j<n/2) : Args context state arguments
    [.pointer (wordPointer tableObject (j*12)),.pointer (wordPointer tableObject ((j-1)*12)),
      .pointer (wordPointer workObject 128),.pointer (wordPointer workObject 0)] state := by
  have outBound : j*12<n/2*12 := by omega
  have aBound : (j-1)*12<n/2*12 := by omega
  have out : Eval context state (arguments[0]'(by decide)) (.pointer (wordPointer tableObject (j*12))) state := by
    exact .paren (.binaryLR (.variable (h.locals.lookup Var.twiddle) (h.locals.read Var.twiddle)) (offset_eval context h false)
      (by simpa only [binary,values,Nat.zero_add,Option.map_some,Bool.false_eq_true,ite_false,ite_true] using
        congrArg (Option.map Value.pointer) (slice_pointer_add h.table (start:=0) (i:=j*12) (by omega))))
  have prev : Eval context state (arguments[1]'(by decide)) (.pointer (wordPointer tableObject ((j-1)*12))) state := by
    exact .paren (.binaryLR (.variable (h.locals.lookup Var.twiddle) (h.locals.read Var.twiddle)) (offset_eval context h true)
      (by simpa only [binary,values,Nat.zero_add,Option.map_some,Bool.false_eq_true,ite_false,ite_true] using
        congrArg (Option.map Value.pointer) (slice_pointer_add h.table (start:=0) (i:=(j-1)*12) (by omega))))
  exact ComplexSource.four_arguments out prev (.variable (h.locals.lookup Var.root) (h.locals.read Var.root))
    (.variable (h.locals.lookup Var.work) (h.locals.read Var.work))
end Evaluation

#print axioms actual_w4_loop
#print axioms actual_fap_loop
#print axioms condition_eval
#print axioms arguments_eval
end RH080Next.FFTPV.TwiddleSource
