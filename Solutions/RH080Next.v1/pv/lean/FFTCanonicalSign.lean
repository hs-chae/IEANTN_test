/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCopySourceFinal
import FFTWordSubtraction
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CanonicalSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings PureDeterminism

inductive Var where | a | nonzero | j deriving DecidableEq
def name : Var → String | .a => "a" | .nonzero => "nonzero" | .j => "j"
def type : Var → CType | .a => .pointer .u64 | .nonzero | .j => .u64
def digitSum (old : Nat → Nat) (start j : Nat) : Nat := ∑i ∈ Finset.range j, old (start+i)
def values (object start : Nat) (old : Nat → Nat) (j : Nat) : Var → Value
  | .a => .pointer (wordPointer object start)
  | .nonzero => .integer (integer64 (digitSum old start j))
  | .j => .integer (integer64 j)

def sumExpr : Expr := .paren (.binary .add (.variable "nonzero") (.index (.variable "a") (.variable "j")))
def sumStmt : Stmt := .assign (.variable "nonzero") sumExpr
def increment : Stmt := .assign (.variable "j") (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL"))))
def condition : Expr := .binary .lt (.variable "j") (.literal (.integer 5 "ULL"))
def loopBody : Stmt := .block [sumStmt, increment]
def loop : Stmt := .whileLoop condition loopBody

def signStore : Stmt := .assign (.index (.variable "a") (.literal (.integer 5 "ULL"))) (.literal (.integer 0 "ULL"))
def zeroTest : Expr := .binary .eq (.variable "nonzero") (.literal (.integer 0 "ULL"))
def canonicalBranch : Stmt := .ite zeroTest (.block [signStore]) none

theorem actual_body : FFTRecursivePV.canonical_sign_ast.body = .block [
    .declare .u64 "nonzero" (some (.literal (.integer 0 "ULL"))),
    .declare .u64 "j" (some (.literal (.integer 0 "ULL"))), loop, canonicalBranch,
    .returnValue (some (.literal (.integer 0 "ULL")))] := by rfl

theorem digitSum_zero (old : Nat → Nat) (start : Nat) : digitSum old start 0 = 0 := by simp [digitSum]
theorem digitSum_succ (old : Nat → Nat) (start j : Nat) :
    digitSum old start (j+1) = digitSum old start j + old (start+j) := by simp [digitSum, Finset.sum_range_succ]

theorem digitSum_fits (old : Nat → Nat) (start j : Nat) (hj : j ≤ 5)
    (digits : ∀i, i < 5 → old (start+i) < 1000000000) : digitSum old start j < 2^64 := by
  have hs : digitSum old start j ≤ j*1000000000 := by
    calc digitSum old start j ≤ ∑i ∈ Finset.range j, 1000000000 := by
           apply Finset.sum_le_sum
           intro i hi
           exact (digits i (by have h := Finset.mem_range.mp hi; omega)).le
         _ = j*1000000000 := by simp
  omega

/-- Actual input allocation and the source's running sum/counter slots. -/
structure View {F : Type} (state : State F) (object size start owner : Nat)
    (ids : Var → Nat) (old : Nat → Nat) (j : Nat) : Prop where
  buffer : WordArrayRep state object size old
  locals : Locals state name type ids owner (values object start old j)
  separate : ∀v, object ≠ ids v
  bound : start+6 ≤ size
  digits : ∀i, i < 5 → old (start+i) < 1000000000
  well : WellScoped state
  active : j ≤ 5

theorem View.enter {F : Type} {state : State F} {object size start owner j : Nat}
    {ids : Var → Nat} {old : Nat → Nat} (h : View state object size start owner ids old j) :
    View state.enterScope object size start owner ids old j :=
  ⟨h.buffer, h.locals.enter, h.separate, h.bound, h.digits, wellScoped_enter h.well, h.active⟩

private theorem slot_store_exists {F : Type} {state : State F} {id owner : Nat}
    {ctype : CType} {oldValue : Value} (h : Slot state id owner ctype oldValue)
    (v : Value) (hv : Storable ctype v) : ∃after, state.store (scalarPointer id ctype) v = some after := by
  obtain ⟨oldType, present⟩ := h
  have hsame : oldValue.byteSize = v.byteSize := Option.some.inj (oldType.typeWidth.symm.trans hv.typeWidth)
  rw [hsame] at present
  simp [State.store, scalarPointer, present, scalarObject, State.accessible, hv.typeWidth, hv.converted]

private theorem array_store_frame {F : Type} {before after : State F} {object size : Nat}
    {old : Nat → Nat} (h : WordArrayRep before object size old) {p : Pointer} {v : Value}
    (different : object ≠ p.object) (written : before.store p v = some after) :
    WordArrayRep after object size old := by
  obtain ⟨env, mode, scope, ns, no, outside⟩ := store_frame written
  exact ⟨mode.trans h.1, (outside object different).trans h.2.1, h.2.2⟩

/-- The actual two source assignments implement the true running digit sum.
The base-billion precondition proves no unsigned overflow can occur. -/
theorem contents_execution {F : Type} (context : Context F) {before : State F}
    {object size start owner j : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start owner ids old j) (hj : j < 5) :
    ∃after, ExecList context before [sumStmt, increment] .normal after ∧
      View after object size start owner ids old (j+1) := by
  have hi : start+j < size := by have hb := h.bound; omega
  have fitNext := digitSum_fits old start (j+1) (by omega) h.digits
  obtain ⟨middle, sumWritten⟩ := slot_store_exists (h.locals.slots Var.nonzero)
    (.integer (integer64 (digitSum old start (j+1)))) (ZeroFrame.u64_storable _ fitNext)
  have sumRun : Exec context before sumStmt .normal middle := by
    apply Exec.assign (value := .integer (integer64 (digitSum old start (j+1))))
      (.paren (.binaryLR (.variable (h.locals.lookup Var.nonzero) (h.locals.read Var.nonzero))
        (.load (.index (.variable (h.locals.lookup Var.a) (h.locals.read Var.a))
          (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
          (slice_pointer_add h.buffer hi)) (word_load h.buffer hi))
        (by simp only [values, binary, ← digitSum_succ,
          binary64_add (digitSum old start j) (old (start+j))
            (digitSum_fits old start j h.active h.digits) (h.buffer.2.2 _ hi)
            (by simpa only [digitSum_succ] using fitNext), Option.map_some])))
      (.variable (h.locals.lookup Var.nonzero))
    exact sumWritten
  have lm := h.locals.store Var.nonzero (.integer (integer64 (digitSum old start (j+1))))
    (ZeroFrame.u64_storable _ fitNext) sumWritten
  have bufferM := array_store_frame h.buffer (h.separate Var.nonzero) sumWritten
  obtain ⟨after, counterWritten⟩ := slot_store_exists (lm.slots Var.j)
    (.integer (integer64 (j+1))) (ZeroFrame.u64_storable _ (by omega))
  have counterRun : Exec context middle increment .normal after := by
    apply Exec.assign (value := .integer (integer64 (j+1)))
      (.paren (.binaryLR (.variable (lm.lookup Var.j) (lm.read Var.j))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp [values, Function.update, binary, binary64_add j 1 (by omega) (by norm_num) (by omega)])))
      (.variable (lm.lookup Var.j))
    exact counterWritten
  have la := lm.store Var.j (.integer (integer64 (j+1))) (ZeroFrame.u64_storable _ (by omega)) counterWritten
  have eqValues : Function.update (Function.update (values object start old j) Var.nonzero
      (.integer (integer64 (digitSum old start (j+1))))) Var.j (.integer (integer64 (j+1))) =
      values object start old (j+1) := by
    funext v
    cases v <;> simp [values, Function.update]
  rw [eqValues] at la
  exact ⟨after, .cons sumRun (.cons counterRun .nil), array_store_frame bufferM (h.separate Var.j) counterWritten,
    la, h.separate, h.bound, h.digits, wellScoped_store (wellScoped_store h.well sumWritten) counterWritten, by omega⟩

private theorem wordArray_leave {F : Type} {state : State F} {object size scope restore : Nat}
    {environment : List (String × Pointer)} {old : Nat → Nat} (h : WordArrayRep state object size old) :
    WordArrayRep {state.leaveScope scope environment with scope := restore} object size old := by
  refine ⟨h.1, ?_, h.2.2⟩
  change (state.objects object).map _ = some _
  rw [h.2.1]
  simp [wordObject]

theorem block_execution {F : Type} (context : Context F) {before : State F}
    {object size start owner j : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start owner ids old j) (hj : j < 5) :
    ∃after, Exec context before loopBody .normal after ∧ View after object size start owner ids old (j+1) := by
  obtain ⟨middle, run, hm⟩ := contents_execution context h.enter hj
  let after : State F := {middle.leaveScope before.nextScope before.environment with scope := before.scope}
  have blockRun : Exec context before loopBody .normal after := .block (by rfl) run (by rfl)
  have effect := SourceNoAlloc.exec_effect blockRun
    (by simp [loopBody, sumStmt, sumExpr, increment, SourceNoAlloc.Only, SourcePure.CallFree]) h.well
  have different : before.nextScope ≠ owner := by have ho := h.locals.bound; omega
  have la := hm.locals.leave different before.environment h.locals.lookup before.scope
  exact ⟨after, blockRun, wordArray_leave (environment := before.environment) (restore := before.scope) hm.buffer,
    la, hm.separate, hm.bound, hm.digits, effect.well, hm.active⟩

private theorem condition_execution {F : Type} (context : Context F) {before : State F}
    {object size start owner j : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start owner ids old j) :
    Eval context before condition (.integer (.boolean (decide (j < 5)))) before := by
  exact .binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
    (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
    (by simp only [values, binary, binary64_lt j 5 (by have ha := h.active; omega) (by norm_num), Option.map_some])

theorem loop_execution {F : Type} (context : Context F) (steps : Nat) {before : State F}
    {object size start owner j : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start owner ids old j) (remaining : j+steps = 5) :
    ∃after, Exec context before loop .normal after ∧ View after object size start owner ids old 5 := by
  induction steps generalizing before j with
  | zero =>
    have he : j = 5 := by omega
    subst j
    exact ⟨before, .whileFalse (condition_execution context h)
      (by decide), h⟩
  | succ steps ih =>
    have hj : j < 5 := by omega
    obtain ⟨middle, first, hm⟩ := block_execution context h hj
    obtain ⟨after, rest, ha⟩ := ih hm (by omega)
    refine ⟨after, .whileNext (condition_execution context h) ?_ first rest, ha⟩
    simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed, hj]

def canonicalData (old : Nat → Nat) (start : Nat) : Nat → Nat :=
  if digitSum old start 5 = 0 then Function.update old (start+5) 0 else old

theorem canonicalData_digit (old : Nat → Nat) (start i : Nat) (hi : i < 5) :
    canonicalData old start (start+i) = old (start+i) := by
  by_cases hz : digitSum old start 5 = 0
  · simp [canonicalData, hz, Function.update_of_ne (show start+i ≠ start+5 by omega)]
  · simp [canonicalData, hz]

theorem canonicalData_sign (old : Nat → Nat) (start : Nat) :
    canonicalData old start (start+5) = if digitSum old start 5 = 0 then 0 else old (start+5) := by
  by_cases hz : digitSum old start 5 = 0 <;> simp [canonicalData, hz, Function.update]

private theorem zero_test_execution {F : Type} (context : Context F) {before : State F}
    {object size start owner : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start owner ids old 5) :
    Eval context before zeroTest (.integer (.boolean (decide (digitSum old start 5 = 0)))) before := by
  exact .binaryLR (.variable (h.locals.lookup Var.nonzero) (h.locals.read Var.nonzero))
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by simp only [values, binary, binary64_eq (digitSum old start 5) 0
      (digitSum_fits old start 5 (by omega) h.digits) (by norm_num), Option.map_some])

/-- Actual final source branch changes the sign word exactly when all five
base-billion digits sum to zero. Its whole allocation remains represented. -/
theorem canonical_branch_execution {F : Type} (context : Context F) {before : State F}
    {object size start owner : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start owner ids old 5) :
    ∃after, Exec context before canonicalBranch .normal after ∧
      WordArrayRep after object size (canonicalData old start) := by
  by_cases hz : digitSum old start 5 = 0
  · have hi : start+5 < size := by have hb := h.bound; omega
    obtain ⟨middle, written, rep⟩ := word_store_with_rep h.enter.buffer hi (by norm_num : 0 < 2^64)
    have storeRun : Exec context before.enterScope signStore .normal middle :=
      .assign (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
        (.index (.variable (h.locals.enter.lookup Var.a) (h.locals.enter.read Var.a))
          (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
          (slice_pointer_add h.enter.buffer hi)) written
    let after : State F := {middle.leaveScope before.nextScope before.environment with scope := before.scope}
    have branch : Exec context before (.block [signStore]) .normal after :=
      .block (by rfl) (.cons storeRun .nil) (by rfl)
    refine ⟨after, .ifTrue (zero_test_execution context h) ?_ branch, ?_⟩
    · simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed, hz]
    · simpa only [canonicalData, if_pos hz] using
        wordArray_leave (environment := before.environment) (restore := before.scope) rep
  · refine ⟨before, .ifFalse (zero_test_execution context h) ?_, ?_⟩
    · simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed, hz]
    · simpa only [canonicalData, if_neg hz] using h.buffer

def localWrites (ids : Var → Nat) : List (String × Pointer) :=
  [("nonzero", scalarPointer (ids Var.nonzero) .u64), ("j", scalarPointer (ids Var.j) .u64)]

private theorem loop_bindings {F : Type} {before : State F} {object size start owner j : Nat}
    {ids : Var → Nat} {old : Nat → Nat} (h : View before object size start owner ids old j) :
    SourceArrayFrame.Bindings before (localWrites ids) [] := by
  constructor
  · intro actualName pointer member
    simp only [localWrites, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.locals.lookup Var.nonzero
    · exact h.locals.lookup Var.j
  · intro item member; cases member
  · intro item member; cases member

/-- The digit-sum loop modifies only its two real local slots. -/
theorem loop_frame {F : Type} {context : Context F} {before after : State F}
    {object size start owner j : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start owner ids old j) {flow : Flow}
    (run : Exec context before loop flow after) :
    ScanFrame.Frame before after [ids Var.nonzero, ids Var.j] := by
  have only : SourceArrayFrame.Only (localWrites ids) [] loop := by
    simp [loop, loopBody, sumStmt, sumExpr, increment, SourceArrayFrame.Only,
      SourceArrayFrame.Writable, localWrites]
  have noAlloc : SourceNoAlloc.Only loop := by
    simp [loop, condition, loopBody, sumStmt, sumExpr, increment, SourceNoAlloc.Only, SourcePure.CallFree]
  have frame := SourceArrayFrame.exec_frame run only noAlloc h.well (loop_bindings h)
  simpa [SourceArrayFrame.writes, localWrites, scalarPointer] using frame

def branchArrays (ids : Var → Nat) (object start : Nat) : List SourceArrayFrame.ArrayBinding :=
  [⟨"a", scalarPointer (ids Var.a) (.pointer .u64), wordPointer object start⟩]

/-- Every final source branch execution frames all other caller allocations. -/
theorem canonical_branch_frame {F : Type} {context : Context F} {before after : State F}
    {object size start owner : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start owner ids old 5) {flow : Flow}
    (run : Exec context before canonicalBranch flow after) : ScanFrame.Frame before after [object] := by
  have bindings : SourceArrayFrame.Bindings before [] (branchArrays ids object start) := by
    constructor
    · intro actualName pointer member; cases member
    · intro item member
      simp only [branchArrays, List.mem_singleton] at member
      subst item
      exact ⟨h.locals.lookup Var.a, h.locals.read Var.a⟩
    · intro item member
      simp only [branchArrays, List.mem_singleton] at member
      subst item
      simpa [SourceArrayFrame.writes, branchArrays, wordPointer, scalarPointer] using Ne.symm (h.separate Var.a)
  have only : SourceArrayFrame.Only [] (branchArrays ids object start) canonicalBranch := by
    simp [canonicalBranch, signStore, branchArrays, SourceArrayFrame.Only, SourceArrayFrame.Writable]
  have noAlloc : SourceNoAlloc.Only canonicalBranch := by
    simp [canonicalBranch, zeroTest, signStore, SourceNoAlloc.Only, SourcePure.CallFree]
  have frame := SourceArrayFrame.exec_frame run only noAlloc h.well bindings
  simpa [SourceArrayFrame.writes, branchArrays, wordPointer] using frame

#print axioms canonical_branch_execution
#print axioms loop_frame
#print axioms canonical_branch_frame

#print axioms actual_body
#print axioms digitSum_fits
#print axioms contents_execution
#print axioms loop_execution
end RH080Next.FFTPV.CanonicalSource
