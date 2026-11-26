/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixAST
import FFTProductBindings
import FFTCanonicalCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ApplicationBirthFrame ProductInner

inductive LVar where | work | lost | i deriving DecidableEq
def lostName : LVar → String | .work => "work" | .lost => "lost" | .i => "i"
def lostType : LVar → CType | .work => .pointer .u64 | .lost | .i => .u64
def lostValues (object start : Nat) (data : Nat → Nat) (j : Nat) : LVar → Value
  | .work => .pointer (wordPointer object start)
  | .lost => .integer (integer64 (CanonicalSource.digitSum data start j))
  | .i => .integer (integer64 j)

/-- Actual persistent/function/temporary owners remain separate. The source
loop reads four low product digits and changes only lost and i. -/
structure LostView {F : Type} (state : State F) (object size start : Nat)
    (ids owners : LVar → Nat) (data : Nat → Nat) (j : Nat) : Prop where
  work : WordArrayRep state object size data
  locals : Bindings state lostName lostType ids owners (lostValues object start data j)
  separate : ∀x, object ≠ ids x
  bound : start+10 ≤ size
  digits : ∀k, k<10 → data (start+k)<1000000000
  well : WellScoped state
  active : j≤4

theorem LostView.enter {F : Type} {state : State F} {object size start j : Nat}
    {ids owners : LVar → Nat} {data : Nat → Nat} (h : LostView state object size start ids owners data j) :
    LostView state.enterScope object size start ids owners data j :=
  ⟨h.work, h.locals.enter, h.separate, h.bound, h.digits, wellScoped_enter h.well, h.active⟩

private theorem slot_store_exists {F : Type} {state : State F} {id owner : Nat}
    {ctype : CType} {old : Value} (h : Slot state id owner ctype old)
    (v : Value) (hv : Storable ctype v) : ∃after, state.store (scalarPointer id ctype) v = some after := by
  obtain ⟨ht, present⟩ := h
  have same : old.byteSize=v.byteSize := Option.some.inj (ht.typeWidth.symm.trans hv.typeWidth)
  rw [same] at present
  simp [State.store, scalarPointer, present, scalarObject, State.accessible, hv.typeWidth, hv.converted]

private theorem array_store_frame {F : Type} {before after : State F} {object size : Nat}
    {data : Nat → Nat} (h : WordArrayRep before object size data) {p : Pointer} {v : Value}
    (different : object ≠ p.object) (stored : before.store p v=some after) : WordArrayRep after object size data := by
  obtain ⟨env, mode, scope, ns, no, outside⟩ := SourceLocals.store_frame stored
  exact ⟨mode.trans h.1, (outside object different).trans h.2.1, h.2.2⟩

theorem lost_contents_execution {F : Type} (context : Context F) {before : State F}
    {object size start j : Nat} {ids owners : LVar → Nat} {data : Nat → Nat}
    (h : LostView before object size start ids owners data j) (hj : j<4) :
    ∃after, ExecList context before [lostStore, increment] .normal after ∧
      LostView after object size start ids owners data (j+1) := by
  have hi : start+j<size := by have hb:=h.bound;omega
  have digits5 : ∀k,k<5 → data (start+k)<1000000000 := fun k hk => h.digits k (by omega)
  have fitNext := CanonicalSource.digitSum_fits data start (j+1) (by omega) digits5
  obtain ⟨middle, sumWritten⟩ := slot_store_exists (h.locals.slots LVar.lost)
    (.integer (integer64 (CanonicalSource.digitSum data start (j+1)))) (ZeroFrame.u64_storable _ fitNext)
  have sumRun : Exec context before lostStore .normal middle := by
    apply Exec.assign (value := .integer (integer64 (CanonicalSource.digitSum data start (j+1))))
      (.paren (.binaryLR (.variable (h.locals.lookup LVar.lost) (h.locals.read LVar.lost))
        (.load (.index (.variable (h.locals.lookup LVar.work) (h.locals.read LVar.work))
          (.variable (h.locals.lookup LVar.i) (h.locals.read LVar.i))
          (slice_pointer_add h.work hi)) (word_load h.work hi))
        (by simp only [lostValues, binary, ← CanonicalSource.digitSum_succ,
          binary64_add (CanonicalSource.digitSum data start j) (data (start+j))
            (CanonicalSource.digitSum_fits data start j (by have a:=h.active;omega) digits5)
            (h.work.2.2 _ hi) (by simpa only [CanonicalSource.digitSum_succ] using fitNext), Option.map_some])))
      (.variable (h.locals.lookup LVar.lost))
    exact sumWritten
  have lm := h.locals.store LVar.lost (.integer (integer64 (CanonicalSource.digitSum data start (j+1))))
    (ZeroFrame.u64_storable _ fitNext) sumWritten
  have workM := array_store_frame h.work (h.separate LVar.lost) sumWritten
  obtain ⟨after, counterWritten⟩ := slot_store_exists (lm.slots LVar.i)
    (.integer (integer64 (j+1))) (ZeroFrame.u64_storable _ (by omega))
  have counterRun : Exec context middle increment .normal after := by
    apply Exec.assign (value := .integer (integer64 (j+1)))
      (.paren (.binaryLR (.variable (lm.lookup LVar.i) (lm.read LVar.i))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp [lostValues, Function.update, binary, binary64_add j 1 (by omega) (by norm_num) (by omega)])))
      (.variable (lm.lookup LVar.i))
    exact counterWritten
  have la := lm.store LVar.i (.integer (integer64 (j+1))) (ZeroFrame.u64_storable _ (by omega)) counterWritten
  have eqValues : Function.update (Function.update (lostValues object start data j) LVar.lost
      (.integer (integer64 (CanonicalSource.digitSum data start (j+1))))) LVar.i (.integer (integer64 (j+1))) =
      lostValues object start data (j+1) := by
    funext v
    cases v <;> simp [lostValues, Function.update]
  rw [eqValues] at la
  exact ⟨after, .cons sumRun (.cons counterRun .nil), array_store_frame workM (h.separate LVar.i) counterWritten,
    la, h.separate, h.bound, h.digits, wellScoped_store (wellScoped_store h.well sumWritten) counterWritten, by omega⟩

private theorem wordArray_leave {F : Type} {state : State F} {object size scope restore : Nat}
    {environment : List (String × Pointer)} {data : Nat → Nat} (h : WordArrayRep state object size data) :
    WordArrayRep {state.leaveScope scope environment with scope:=restore} object size data := by
  refine ⟨h.1, ?_, h.2.2⟩
  change (state.objects object).map _=some _
  rw [h.2.1]
  simp [wordObject]

theorem lost_block_execution {F : Type} (context : Context F) {before : State F}
    {object size start j : Nat} {ids owners : LVar → Nat} {data : Nat → Nat}
    (h : LostView before object size start ids owners data j) (hj : j<4) :
    ∃after, Exec context before lostBody .normal after ∧ LostView after object size start ids owners data (j+1) := by
  obtain ⟨middle, run, hm⟩ := lost_contents_execution context h.enter hj
  let after : State F := {middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have blockRun : Exec context before lostBody .normal after := .block (by rfl) run (by rfl)
  have effect := SourceNoAlloc.exec_effect blockRun
    (by simp [lostBody, lostStore, lostExpression, increment, v, lit, SourceNoAlloc.Only, SourcePure.CallFree]) h.well
  have different : ∀x, before.nextScope ≠ owners x := by intro x;have ho:=h.locals.bound x;omega
  have la := hm.locals.leave (restore:=before.scope) different before.environment h.locals.lookup
  exact ⟨after, blockRun, wordArray_leave (environment:=before.environment) (restore:=before.scope) hm.work,
    la, hm.separate, hm.bound, hm.digits, effect.well, hm.active⟩

private theorem lost_condition_execution {F : Type} (context : Context F) {before : State F}
    {object size start j : Nat} {ids owners : LVar → Nat} {data : Nat → Nat}
    (h : LostView before object size start ids owners data j) :
    Eval context before lostCondition (.integer (.boolean (decide (j<4)))) before := by
  exact .binaryLR (.variable (h.locals.lookup LVar.i) (h.locals.read LVar.i))
    (.literal (.integer 4 "ULL") _ (.integer (integer64 4)) (by rfl))
    (by simp only [lostValues, binary, binary64_lt j 4 (by have ha:=h.active;omega) (by norm_num), Option.map_some])

/-- The actual source lost-low-digit loop terminates with the exact sum of
its four true workspace words, preserving the complete workspace. -/
theorem lost_loop_execution {F : Type} (context : Context F) (steps : Nat) {before : State F}
    {object size start j : Nat} {ids owners : LVar → Nat} {data : Nat → Nat}
    (h : LostView before object size start ids owners data j) (remaining : j+steps=4) :
    ∃after, Exec context before lostLoop .normal after ∧ LostView after object size start ids owners data 4 := by
  induction steps generalizing before j with
  | zero =>
    have equal : j=4 := by omega
    subst j
    exact ⟨before, .whileFalse (lost_condition_execution context h) (by decide), h⟩
  | succ steps ih =>
    have hj : j<4 := by omega
    obtain ⟨middle, first, hm⟩ := lost_block_execution context h hj
    obtain ⟨after, rest, ha⟩ := ih hm (by omega)
    refine ⟨after, .whileNext (lost_condition_execution context h) ?_ first rest, ha⟩
    simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed, hj]

def lostWrites (ids : LVar → Nat) : List (String × Pointer) :=
  [("lost", scalarPointer (ids LVar.lost) .u64), ("i", scalarPointer (ids LVar.i) .u64)]

theorem lost_loop_frame {F : Type} {context : Context F} {before after : State F}
    {object size start j : Nat} {ids owners : LVar → Nat} {data : Nat → Nat}
    (h : LostView before object size start ids owners data j) {flow : Flow}
    (run : Exec context before lostLoop flow after) :
    ScanFrame.Frame before after [ids LVar.lost, ids LVar.i] := by
  have bindings : SourceArrayFrame.Bindings before (lostWrites ids) [] := by
    constructor
    · intro actualName pointer member
      simp only [lostWrites, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at member
      rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact h.locals.lookup LVar.lost
      · exact h.locals.lookup LVar.i
    · intro item member; cases member
    · intro item member; cases member
  have only : SourceArrayFrame.Only (lostWrites ids) [] lostLoop := by
    simp [lostLoop, lostBody, lostStore, increment, v, lit, SourceArrayFrame.Only, SourceArrayFrame.Writable, lostWrites]
  have noAlloc : SourceNoAlloc.Only lostLoop := by
    simp [lostLoop, lostCondition, lostBody, lostStore, lostExpression, increment, v, lit,
      SourceNoAlloc.Only, SourcePure.CallFree]
  have frame := SourceArrayFrame.exec_frame run only noAlloc h.well bindings
  simpa [SourceArrayFrame.writes, lostWrites, scalarPointer] using frame

theorem lost_loop_unique {F : Type} (context : Context F) : CompareSource.Unique context lostLoop := by
  apply CompareSource.while_unique (by simp [lostCondition, v, lit, SourcePure.CallFree])
  intro before a b fa fb first second
  exact PureDeterminism.block_unique
    (by simp [lostBody, lostStore, lostExpression, increment, v, lit, PureDeterminism.Simple, SourcePure.CallFree]) first second

/-- Universal correctness: every actual source lost loop has the exact same
normal result and retains all allocations outside its two scalar slots. -/
theorem every_lost_loop {F : Type} {context : Context F} {before after : State F}
    {object size start j : Nat} {ids owners : LVar → Nat} {data : Nat → Nat}
    (h : LostView before object size start ids owners data j) {flow : Flow}
    (run : Exec context before lostLoop flow after) :
    flow = .normal ∧ LostView after object size start ids owners data 4 ∧
      ScanFrame.Frame before after [ids LVar.lost, ids LVar.i] := by
  obtain ⟨canonical, known, view⟩ := lost_loop_execution context (4-j) h (by have hj:=h.active;omega)
  obtain ⟨flowEq,stateEq⟩ := lost_loop_unique context run known
  cases stateEq
  exact ⟨flowEq,view,lost_loop_frame h run⟩

#print axioms every_lost_loop

#print axioms lost_contents_execution
#print axioms lost_loop_execution
end RH080Next.FFTPV.MultiplySuffix
