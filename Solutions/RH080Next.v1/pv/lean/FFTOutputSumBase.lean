/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddMagnitudeSource
import FFTComplexSourceFinal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.OutputSumSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

inductive Var where | n | output | total | status | i deriving DecidableEq

def name : Var→String | .n=>"n" | .output=>"output" | .total=>"total" | .status=>"status" | .i=>"i"
def type : Var→CType | .output | .total=>.pointer .u64 | _=>.u64

def values (outputObject workObject n i : Nat) : Var→Value
  | .n=>.integer (integer64 n)
  | .output=>.pointer (wordPointer outputObject 0)
  | .total=>.pointer (wordPointer workObject 192)
  | .status=>.integer (integer64 0)
  | .i=>.integer (integer64 i)

def arguments : List Expr:=[.variable "total",
  .paren (.binary .add (.variable "output") (.paren (.binary .mul (.variable "i") (.literal (.integer 12 "ULL"))))),
  .literal (.integer 6 "ULL")]
def callStmt : Stmt:=StatusCall.statement "add_magnitude" arguments
def advance : Stmt:=.assign (.variable "i") (.paren (.binary .add (.variable "i") (.literal (.integer 1 "ULL"))))
def loopBody : Stmt:=.block [callStmt,advance]
def condition : Expr:=.binary .lt (.variable "i") (.variable "n")
def loop : Stmt:=.whileLoop condition loopBody

theorem actual_w4_loop : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[25]?=some loop := by rfl
theorem actual_fap_loop : (ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body)[25]?=some loop := by rfl

def partialSum (samples : Nat→FFT.IntegerModel.CInt) (i : Nat) : Nat:=∑k∈Finset.range i,(samples k).1.natAbs

theorem partialSum_succ (samples : Nat→FFT.IntegerModel.CInt) (i : Nat) :
    partialSum samples (i+1)=partialSum samples i+(samples i).1.natAbs:=Finset.sum_range_succ _ _

theorem partialSum_le {samples : Nat→FFT.IntegerModel.CInt} {n i : Nat} (inside : i≤n)
    (bound : ∀k,k<n → (samples k).1.natAbs≤400*10^36) : partialSum samples i≤ i*(400*10^36) := by
  calc
    partialSum samples i≤∑k∈Finset.range i,(400*10^36 : Nat):=by
      apply Finset.sum_le_sum
      intro k hk
      exact bound k (lt_of_lt_of_le (Finset.mem_range.mp hk) inside)
    _=i*(400*10^36):=by simp

structure View {F : Type} (state : State F) (outputObject workObject n : Nat)
    (ids : Var→Nat) (owner i : Nat) (outputData workData : Nat→Nat) (samples : Nat→FFT.IntegerModel.CInt) (pending : Bool:=false) : Prop where
  locals : Locals state name type ids owner (values outputObject workObject n i)
  output : WordArrayRep state outputObject (n*12) outputData
  work : WordArrayRep state workObject 512 workData
  different : outputObject≠workObject
  separate : ∀v,outputObject≠ids v ∧ workObject≠ids v
  nbound : 1≤n ∧ n≤16777216
  active : i≤n
  outputDigits : ∀k,k<n → ∀d,d<5 → outputData (k*12+d)<1000000000
  outputValues : ∀k,k<n → (ComplexSource.pair outputData (k*12)).1=(samples k).1
  outputSmall : ∀k,k<n → (samples k).1.natAbs≤400*10^36
  totalDigits : ∀d,d<6 → workData (192+d)<1000000000
  totalValue : FFT.Limbs.magnitude 1000000000 6 (fun d=>workData (192+d))=partialSum samples i+(if pending then (samples i).1.natAbs else 0)
  well : WellScoped state

theorem View.enter {F : Type} {state : State F} {outputObject workObject n owner i : Nat}
    {ids : Var→Nat} {outputData workData : Nat→Nat} {samples : Nat→FFT.IntegerModel.CInt} {pending : Bool}
    (h : View state outputObject workObject n ids owner i outputData workData samples pending) :
    View state.enterScope outputObject workObject n ids owner i outputData workData samples pending:=
  ⟨h.locals.enter,h.output,h.work,h.different,h.separate,h.nbound,h.active,h.outputDigits,h.outputValues,h.outputSmall,h.totalDigits,h.totalValue,wellScoped_enter h.well⟩

theorem condition_eval {F : Type} (context : Context F) {state : State F} {outputObject workObject n owner i : Nat}
    {ids : Var→Nat} {outputData workData : Nat→Nat} {samples : Nat→FFT.IntegerModel.CInt}
    (h : View state outputObject workObject n ids owner i outputData workData samples) :
    Eval context state condition (.integer (.boolean (decide (i<n)))) state := by
  have hn : n<2^64:=by have b:=h.nbound;omega
  have hi : i<2^64:=by have b:=h.active;omega
  exact .binaryLR (.variable (h.locals.lookup Var.i) (h.locals.read Var.i))
    (.variable (h.locals.lookup Var.n) (h.locals.read Var.n))
    (by simp only [values,binary,binary64_lt i n hi hn,Option.map_some])

#print axioms actual_w4_loop
#print axioms actual_fap_loop
#print axioms partialSum_le
#print axioms condition_eval
end RH080Next.FFTPV.OutputSumSource
