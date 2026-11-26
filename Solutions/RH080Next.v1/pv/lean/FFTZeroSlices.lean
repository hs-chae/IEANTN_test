/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCopyAllExecutions
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ZeroSlice
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings PureDeterminism
abbrev Var := ZeroFrame.Var
abbrev name := ZeroFrame.name
abbrev type := ZeroFrame.type

def value (object start length j : Nat) : Var → Value
  | .a => .pointer (wordPointer object start)
  | .n => .integer (integer64 length)
  | .j => .integer (integer64 j)
def zeroData (old : Nat → Nat) (start j : Nat) : Nat → Nat :=
  CopyLoop.prefixData old (fun _ => 0) start j

theorem zeroData_zero (old : Nat → Nat) (start : Nat) : zeroData old start 0 = old :=
  CopyLoop.prefixData_zero old (fun _ => 0) start
theorem zeroData_step (old : Nat → Nat) (start j : Nat) :
    Function.update (zeroData old start j) (start+j) 0 = zeroData old start (j+1) :=
  CopyLoop.prefixData_step old (fun _ => 0) start j

theorem zeroData_inside (old : Nat → Nat) (start length i : Nat) (hi : i < length) :
    zeroData old start length (start+i) = 0 := by
  simp [zeroData, CopyLoop.prefixData, show start ≤ start+i ∧ start+i < start+length by omega]

theorem zeroData_outside (old : Nat → Nat) (start length i : Nat)
    (hi : i < start ∨ start+length ≤ i) : zeroData old start length i = old i := by
  simp [zeroData, CopyLoop.prefixData, show ¬(start ≤ i ∧ i < start+length) by omega]

/-- Already initialized actual typed allocation. The reset interval may be a
proper subrange at an arbitrary offset; its complement is retained exactly. -/
structure View {F : Type} (state : State F) (object size start length owner : Nat)
    (ids : Var → Nat) (old : Nat → Nat) (j : Nat) : Prop where
  buffer : WordArrayRep state object size (zeroData old start j)
  locals : Locals state name type ids owner (value object start length j)
  separate : ∀v, object ≠ ids v
  bound : start+length ≤ size
  well : WellScoped state
  active : j ≤ length
  fits : length < 2^64

theorem View.enter {F : Type} {state : State F} {object size start length owner j : Nat}
    {ids : Var → Nat} {old : Nat → Nat} (h : View state object size start length owner ids old j) :
    View state.enterScope object size start length owner ids old j :=
  ⟨h.buffer, h.locals.enter, h.separate, h.bound, wellScoped_enter h.well, h.active, h.fits⟩

private theorem locals_store_outside {F I : Type} {before after : State F}
    {names : I → String} {types : I → CType} {ids : I → Nat} {owner : Nat} {values : I → Value}
    (h : Locals before names types ids owner values) {p : Pointer} {v : Value}
    (different : ∀i, ids i ≠ p.object) (stored : before.store p v = some after) :
    Locals after names types ids owner values := by
  obtain ⟨env, mode, scope, ns, no, outside⟩ := store_frame stored
  exact ⟨fun i => by rw [env]; exact h.lookup i,
    fun i => ⟨(h.slots i).storable, by rw [outside (ids i) (different i)]; exact (h.slots i).object⟩,
    h.distinct, by rw [ns]; exact h.bound⟩

private theorem slot_store_exists {F : Type} {state : State F} {id owner : Nat}
    {ctype : CType} {oldValue : Value} (h : Slot state id owner ctype oldValue)
    (v : Value) (hv : Storable ctype v) : ∃after, state.store (scalarPointer id ctype) v = some after := by
  obtain ⟨oldType, present⟩ := h
  have hsame : oldValue.byteSize = v.byteSize := Option.some.inj (oldType.typeWidth.symm.trans hv.typeWidth)
  rw [hsame] at present
  simp [State.store, scalarPointer, present, scalarObject, State.accessible, hv.typeWidth, hv.converted]

/-- The actual two assignments in zero_words, including typed pointer indexing
at the real base offset and the unsigned counter's nonoverflow proof. -/
theorem contents_execution {F : Type} (context : Context F) {before : State F}
    {object size start length owner j : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start length owner ids old j) (hj : j < length) :
    ∃after, ExecList context before [zeroStoreStmt, ZeroLoop.increment] .normal after ∧
      View after object size start length owner ids old (j+1) := by
  have hi : start+j < size := by have hb := h.bound; omega
  obtain ⟨middle, writeBuffer, buffer⟩ := word_store_with_rep h.buffer hi (by norm_num : 0 < 2^64)
  rw [zeroData_step] at buffer
  have bufferRun : Exec context before zeroStoreStmt .normal middle :=
    .assign (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
      (.index (.variable (h.locals.lookup ZeroFrame.Var.a) (h.locals.read ZeroFrame.Var.a))
        (.variable (h.locals.lookup ZeroFrame.Var.j) (h.locals.read ZeroFrame.Var.j))
        (slice_pointer_add h.buffer hi)) writeBuffer
  have lm := locals_store_outside h.locals (fun v => Ne.symm (h.separate v)) writeBuffer
  have fits : j+1 < 2^64 := lt_of_le_of_lt (by omega) h.fits
  obtain ⟨after, writeCounter⟩ := slot_store_exists (lm.slots ZeroFrame.Var.j)
    (.integer (integer64 (j+1))) (ZeroFrame.u64_storable (j+1) fits)
  have counterRun : Exec context middle ZeroLoop.increment .normal after := by
    apply Exec.assign (value := .integer (integer64 (j+1)))
      (Eval.paren (Eval.binaryLR (.variable (lm.lookup ZeroFrame.Var.j) (lm.read ZeroFrame.Var.j))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [value, binary, binary64_add j 1 (by omega) (by norm_num) fits, Option.map_some])))
      (.variable (lm.lookup ZeroFrame.Var.j))
    exact writeCounter
  have la := lm.store ZeroFrame.Var.j (.integer (integer64 (j+1))) (ZeroFrame.u64_storable (j+1) fits) writeCounter
  have values : Function.update (value object start length j) ZeroFrame.Var.j (.integer (integer64 (j+1))) =
      value object start length (j+1) := by
    funext v
    cases v <;> simp [value, Function.update]
  rw [values] at la
  obtain ⟨env, mode, scope, ns, no, outside⟩ := store_frame writeCounter
  exact ⟨after, .cons bufferRun (.cons counterRun .nil),
    ⟨mode.trans buffer.1, (outside object (h.separate ZeroFrame.Var.j)).trans buffer.2.1, buffer.2.2⟩,
    la, h.separate, h.bound, wellScoped_store (wellScoped_store h.well writeBuffer) writeCounter,
    by omega, h.fits⟩

private theorem wordArray_leave {F : Type} {state : State F} {object size scope restore : Nat}
    {environment : List (String × Pointer)} {data : Nat → Nat}
    (h : WordArrayRep state object size data) :
    WordArrayRep {state.leaveScope scope environment with scope := restore} object size data := by
  refine ⟨h.1, ?_, h.2.2⟩
  change (state.objects object).map _ = some (wordObject size data)
  rw [h.2.1]
  simp [wordObject]

theorem block_execution {F : Type} (context : Context F) {before : State F}
    {object size start length owner j : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start length owner ids old j) (hj : j < length) :
    ∃after, Exec context before ZeroLoop.loopBody .normal after ∧
      View after object size start length owner ids old (j+1) := by
  obtain ⟨middle, run, hm⟩ := contents_execution context h.enter hj
  let after : State F := {middle.leaveScope before.nextScope before.environment with scope := before.scope}
  have blockRun : Exec context before ZeroLoop.loopBody .normal after := .block (by rfl) run (by rfl)
  have effect := SourceNoAlloc.exec_effect blockRun
    (by simp [ZeroLoop.loopBody, ZeroLoop.increment, zeroStoreStmt, SourceNoAlloc.Only, SourcePure.CallFree]) h.well
  have different : before.nextScope ≠ owner := by have ho := h.locals.bound; omega
  have la := hm.locals.leave different before.environment h.locals.lookup before.scope
  exact ⟨after, blockRun,
    wordArray_leave (environment := before.environment) (restore := before.scope) hm.buffer,
    la, hm.separate, hm.bound, effect.well, hm.active, hm.fits⟩

private theorem condition_execution {F : Type} (context : Context F) {before : State F}
    {object size start length owner j : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start length owner ids old j) :
    Eval context before ZeroLoop.condition (.integer (.boolean (decide (j < length)))) before := by
  have computed : Integer.binary .lt (integer64 j) (integer64 length) = some (.boolean (decide (j < length))) := by
    change some (Integer.boolean ((Integer.cast .u64 (j:Int)).toInt < (Integer.cast .u64 (length:Int)).toInt)) = _
    rw [cast64_exact j (lt_of_le_of_lt h.active h.fits), cast64_exact length h.fits, integer64_toInt, integer64_toInt]
    congr 2
    simp
  exact .binaryLR (.variable (h.locals.lookup ZeroFrame.Var.j) (h.locals.read ZeroFrame.Var.j))
    (.variable (h.locals.lookup ZeroFrame.Var.n) (h.locals.read ZeroFrame.Var.n))
    (by simp only [value, binary, computed, Option.map_some])

theorem loop_execution {F : Type} (context : Context F) (steps : Nat) {before : State F}
    {object size start length owner j : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start length owner ids old j) (remaining : j+steps = length) :
    ∃after, Exec context before ZeroLoop.loop .normal after ∧
      View after object size start length owner ids old length := by
  induction steps generalizing before j with
  | zero =>
    have he : j = length := by omega
    subst j
    exact ⟨before, .whileFalse (condition_execution context h)
      (by simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed]), h⟩
  | succ steps ih =>
    have hj : j < length := by omega
    obtain ⟨middle, first, hm⟩ := block_execution context h hj
    obtain ⟨after, rest, ha⟩ := ih hm (by omega)
    refine ⟨after, .whileNext (condition_execution context h) ?_ first rest, ha⟩
    simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed, hj]

def localWrites (ids : Var → Nat) : List (String × Pointer) :=
  [("j", scalarPointer (ids ZeroFrame.Var.j) .u64)]
def arrayWrites (ids : Var → Nat) (object start : Nat) : List SourceArrayFrame.ArrayBinding :=
  [⟨"a", scalarPointer (ids ZeroFrame.Var.a) (.pointer .u64), wordPointer object start⟩]

private theorem view_bindings {F : Type} {before : State F}
    {object size start length owner j : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start length owner ids old j) :
    SourceArrayFrame.Bindings before (localWrites ids) (arrayWrites ids object start) := by
  constructor
  · intro actualName pointer member
    simp only [localWrites, List.mem_singleton, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact h.locals.lookup ZeroFrame.Var.j
  · intro item member
    simp only [arrayWrites, List.mem_singleton] at member
    subst item
    exact ⟨h.locals.lookup ZeroFrame.Var.a, h.locals.read ZeroFrame.Var.a⟩
  · intro item member
    simp only [arrayWrites, List.mem_singleton] at member
    subst item
    have hd : ids ZeroFrame.Var.a ≠ ids ZeroFrame.Var.j := by intro he; have hh := h.locals.distinct he; cases hh
    simpa [SourceArrayFrame.writes, localWrites, arrayWrites, scalarPointer, wordPointer]
      using And.intro hd (Ne.symm (h.separate ZeroFrame.Var.a))

/-- Every reset-loop execution preserves every other caller allocation. -/
theorem loop_frame {F : Type} {context : Context F} {before after : State F}
    {object size start length owner j : Nat} {ids : Var → Nat} {old : Nat → Nat}
    (h : View before object size start length owner ids old j) {flow : Flow}
    (run : Exec context before ZeroLoop.loop flow after) : ScanFrame.Frame before after [ids ZeroFrame.Var.j, object] := by
  have only : SourceArrayFrame.Only (localWrites ids) (arrayWrites ids object start) ZeroLoop.loop := by
    simp [ZeroLoop.loop, ZeroLoop.loopBody, ZeroLoop.increment, zeroStoreStmt,
      SourceArrayFrame.Only, SourceArrayFrame.Writable, localWrites, arrayWrites]
  have noAlloc : SourceNoAlloc.Only ZeroLoop.loop := by
    simp [ZeroLoop.loop, ZeroLoop.condition, ZeroLoop.loopBody, ZeroLoop.increment, zeroStoreStmt,
      SourceNoAlloc.Only, SourcePure.CallFree]
  have hf := SourceArrayFrame.exec_frame run only noAlloc h.well (view_bindings h)
  simpa [SourceArrayFrame.writes, localWrites, arrayWrites, scalarPointer, wordPointer] using hf

theorem block_postcondition {F : Type} {context : Context F} {before after : State F}
    {object size start length owner j : Nat} {ids : Var → Nat} {old : Nat → Nat} {flow : Flow}
    (h : View before object size start length owner ids old j) (hj : j < length)
    (run : Exec context before ZeroLoop.loopBody flow after) :
    flow = .normal ∧ View after object size start length owner ids old (j+1) := by
  obtain ⟨expected, known, view⟩ := block_execution context h hj
  have pure : ∀s ∈ [zeroStoreStmt, ZeroLoop.increment], Simple s := by
    simp [Simple, zeroStoreStmt, ZeroLoop.increment, SourcePure.CallFree]
  obtain ⟨eqFlow, eqState⟩ := block_unique pure known run
  exact ⟨eqFlow.symm, eqState ▸ view⟩

private theorem condition_pure : SourcePure.CallFree ZeroLoop.condition := by
  simp [ZeroLoop.condition, SourcePure.CallFree]

/-- Every allowed source loop execution resets precisely the interval. -/
theorem loop_postcondition {F : Type} {context : Context F} (steps : Nat) {before after : State F}
    {object size start length owner j : Nat} {ids : Var → Nat} {old : Nat → Nat} {flow : Flow}
    (h : View before object size start length owner ids old j) (remaining : j+steps = length)
    (run : Exec context before ZeroLoop.loop flow after) :
    flow = .normal ∧ View after object size start length owner ids old length := by
  induction steps generalizing before after j flow with
  | zero =>
    have he : j = length := by omega
    subst j
    change Exec context before (.whileLoop ZeroLoop.condition ZeroLoop.loopBody) flow after at run
    cases run with
    | whileFalse tested truth =>
      obtain ⟨_, rfl⟩ := eval_unique condition_pure (condition_execution context h) tested
      exact ⟨rfl, h⟩
    | whileNext tested truth body rest =>
      obtain ⟨rfl, _⟩ := eval_unique condition_pure (condition_execution context h) tested
      simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed] at truth
    | whileContinue tested truth body rest =>
      obtain ⟨rfl, _⟩ := eval_unique condition_pure (condition_execution context h) tested
      simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed] at truth
    | whileBreak tested truth body =>
      obtain ⟨rfl, _⟩ := eval_unique condition_pure (condition_execution context h) tested
      simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed] at truth
    | whileExit tested truth body abrupt =>
      obtain ⟨rfl, _⟩ := eval_unique condition_pure (condition_execution context h) tested
      simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed] at truth
  | succ steps ih =>
    have hj : j < length := by omega
    change Exec context before (.whileLoop ZeroLoop.condition ZeroLoop.loopBody) flow after at run
    cases run with
    | whileFalse tested truth =>
      obtain ⟨rfl, _⟩ := eval_unique condition_pure (condition_execution context h) tested
      simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed, hj] at truth
    | whileNext tested truth body rest =>
      obtain ⟨_, rfl⟩ := eval_unique condition_pure (condition_execution context h) tested
      exact ih (block_postcondition h hj body).2 (by omega) rest
    | whileContinue tested truth body rest =>
      obtain ⟨_, rfl⟩ := eval_unique condition_pure (condition_execution context h) tested
      cases (block_postcondition h hj body).1
    | whileBreak tested truth body =>
      obtain ⟨_, rfl⟩ := eval_unique condition_pure (condition_execution context h) tested
      cases (block_postcondition h hj body).1
    | whileExit tested truth body abrupt =>
      obtain ⟨_, rfl⟩ := eval_unique condition_pure (condition_execution context h) tested
      exact False.elim (abrupt.1 (block_postcondition h hj body).1)

#print axioms contents_execution
#print axioms loop_execution
#print axioms loop_frame
#print axioms loop_postcondition
end RH080Next.FFTPV.ZeroSlice
