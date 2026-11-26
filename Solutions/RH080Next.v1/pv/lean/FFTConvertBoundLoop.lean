/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTConvertBoundBase
import ExplicitFFTCompareDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ConvertBoundSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

theorem advance_execution {F : Type} (context : Context F) {before : State F}
    {object size start owner i : Nat} {ids : Var→Nat} {data : Nat→Nat}
    (h : View before object size start ids owner data i) (hi : i<6) :
    ∃after,Exec context before advance .normal after ∧ View after object size start ids owner data (i+1) := by
  have hf : i+1<2^64 := by omega
  obtain ⟨after,written⟩ := ProductInner.slot_store_exists (h.locals.slots Var.i)
    (.integer (integer64 (i+1))) (ZeroFrame.u64_storable (i+1) hf)
  have run : Exec context before advance .normal after := by
    apply Exec.assign (value:=.integer (integer64 (i+1)))
      (Eval.paren (Eval.binaryLR (.variable (h.locals.lookup Var.i) (h.locals.read Var.i))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [values,binary,binary64_add i 1 (by omega) (by norm_num) hf,Option.map_some])))
      (.variable (h.locals.lookup Var.i))
    exact written
  have la := h.locals.store Var.i (.integer (integer64 (i+1))) (ZeroFrame.u64_storable (i+1) hf) written
  have hv : Function.update (values object start i) Var.i (.integer (integer64 (i+1)))=values object start (i+1) := by
    funext v;cases v <;> simp [values,Function.update]
  rw [hv] at la
  obtain ⟨_,mode,_,_,_,outside⟩ := store_frame written
  have ar : WordArrayRep after object size data :=
    ⟨mode.trans h.array.1,(outside object (h.separate Var.i)).trans h.array.2.1,h.array.2.2⟩
  exact ⟨after,run,ar,la,h.separate,h.bound,h.digits,by omega,wellScoped_store h.well written⟩

theorem close_view {F : Type} {context : Context F} {before middle : State F}
    {object size start owner i k : Nat} {ids : Var→Nat} {data : Nat→Nat}
    {body : List Stmt} {flow : Flow} (h : View before object size start ids owner data i)
    (hm : View middle object size start ids owner data k)
    (run : ExecList context before.enterScope body flow middle)
    (only : SourceNoAlloc.Only (.block body)) :
    View {middle.leaveScope before.nextScope before.environment with scope:=before.scope} object size start ids owner data k := by
  have blockRun : Exec context before (.block body) flow
      {middle.leaveScope before.nextScope before.environment with scope:=before.scope} := .block (by rfl) run (by rfl)
  have effect := SourceNoAlloc.exec_effect blockRun only h.well
  have different : before.nextScope≠owner := by have ho:=h.locals.bound;omega
  exact ⟨ComplexSource.word_array_leave hm.array before.nextScope before.scope before.environment,
    hm.locals.leave different before.environment h.locals.lookup before.scope,
    hm.separate,hm.bound,hm.digits,hm.active,effect.well⟩

theorem sentinel_block {F : Type} (context : Context F) {before : State F}
    {object size start owner i : Nat} {ids : Var→Nat} {data : Nat→Nat}
    (h : View before object size start ids owner data i) :
    ∃after,Exec context before (.block [returnSentinel]) (.returned (.integer (integer64 sentinel))) after ∧
      View after object size start ids owner data i := by
  have run : ExecList context before.enterScope [returnSentinel] (.returned (.integer (integer64 sentinel))) before.enterScope :=
    .abrupt (.returnSome (.literal (.integer sentinel "ULL") _ (.integer (integer64 sentinel)) (by rfl))) (by intro h;cases h)
  refine ⟨{before.enterScope.leaveScope before.nextScope before.environment with scope:=before.scope},
    .block (by rfl) run (by rfl),?_⟩
  exact close_view h h.enter run (by simp [returnSentinel,SourceNoAlloc.Only,SourcePure.CallFree])

def stepFlow (data : Nat→Nat) (start i : Nat) : Flow :=
  if data (start+i)=0 then .normal else .returned (.integer (integer64 sentinel))

theorem body_execution {F : Type} (context : Context F) {before : State F}
    {object size start owner i : Nat} {ids : Var→Nat} {data : Nat→Nat}
    (h : View before object size start ids owner data i) (hi : i<6) :
    ∃after k,Exec context before loopBody (stepFlow data start i) after ∧
      View after object size start ids owner data k ∧ (data (start+i)=0 → k=i+1) := by
  have only : SourceNoAlloc.Only loopBody := by
    simp [loopBody,branch,test,returnSentinel,advance,SourceNoAlloc.Only,SourcePure.CallFree]
  by_cases hz : data (start+i)=0
  · have first : Exec context before.enterScope branch .normal before.enterScope :=
      .ifFalse (test_eval context h.enter hi) (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hz])
    obtain ⟨middle,inc,hm⟩ := advance_execution context h.enter hi
    have run : ExecList context before.enterScope [branch,advance] .normal middle := .cons first (.cons inc .nil)
    refine ⟨{middle.leaveScope before.nextScope before.environment with scope:=before.scope},i+1,?_,close_view h hm run only,by simp⟩
    simpa only [loopBody,stepFlow,if_pos hz] using (Exec.block (by rfl) run (by rfl))
  · obtain ⟨middle,ret,hm⟩ := sentinel_block context h.enter
    have run : ExecList context before.enterScope [branch,advance] (.returned (.integer (integer64 sentinel))) middle :=
      .abrupt (.ifTrue (test_eval context h.enter hi)
        (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hz]) ret) (by intro h;cases h)
    refine ⟨{middle.leaveScope before.nextScope before.environment with scope:=before.scope},i,?_,close_view h hm run only,by simp [hz]⟩
    simpa only [loopBody,stepFlow,if_neg hz] using (Exec.block (by rfl) run (by rfl))

def loopFlow (data : Nat→Nat) (start steps i : Nat) : Flow :=
  if allZero data start steps i then .normal else .returned (.integer (integer64 sentinel))

theorem loop_execution {F : Type} (context : Context F) (steps : Nat) {before : State F}
    {object size start owner i : Nat} {ids : Var→Nat} {data : Nat→Nat}
    (h : View before object size start ids owner data i) (finish : i+steps=6) :
    ∃after k,Exec context before loop (loopFlow data start steps i) after ∧
      View after object size start ids owner data k := by
  induction steps generalizing before i with
  | zero =>
    have hi : i=6 := by omega
    subst i
    refine ⟨before,6,?_,h⟩
    exact .whileFalse (condition_eval context h) (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed])
  | succ steps ih =>
    have hi : i<6 := by omega
    obtain ⟨middle,k,body,hm,hk⟩ := body_execution context h hi
    have ct := condition_eval context h
    have tr : (Value.integer (.boolean (decide (i<6)))).truth=some true := by
      simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hi]
    by_cases hz : data (start+i)=0
    · have ke : k=i+1 := hk hz
      subst k
      obtain ⟨after,k,rest,hk⟩ := ih hm (by omega)
      refine ⟨after,k,?_,hk⟩
      have run : Exec context before loop (loopFlow data start steps (i+1)) after := Exec.whileNext ct tr (by simpa only [stepFlow,if_pos hz] using body) rest
      simpa only [loopFlow,allZero,hz,decide_true,Bool.true_and] using run
    · refine ⟨middle,k,?_,hm⟩
      have run : Exec context before loop (.returned (.integer (integer64 sentinel))) middle := Exec.whileExit ct tr (by simpa only [stepFlow,if_neg hz] using body) (by simp)
      simpa only [loopFlow,allZero,hz,decide_false,Bool.false_and,Bool.false_eq_true,if_false] using run

def localWrites (ids : Var→Nat) : List (String×Pointer) := [("i",scalarPointer (ids Var.i) .u64)]

theorem loop_frame {F : Type} {context : Context F} {before after : State F}
    {object size start owner i : Nat} {ids : Var→Nat} {data : Nat→Nat}
    (h : View before object size start ids owner data i) {flow : Flow}
    (run : Exec context before loop flow after) : ScanFrame.Frame before after [ids Var.i] := by
  have bindings : SourceArrayFrame.Bindings before (localWrites ids) [] := by
    constructor
    · intro cname pointer member
      simp only [localWrites,List.mem_singleton,Prod.mk.injEq] at member
      rcases member with ⟨rfl,rfl⟩
      exact h.locals.lookup Var.i
    · intro item member;cases member
    · intro item member;cases member
  have writes : SourceArrayFrame.Only (localWrites ids) [] loop := by
    simp [loop,loopBody,condition,advance,branch,test,returnSentinel,SourceArrayFrame.Only,SourceArrayFrame.Writable,localWrites]
  have noalloc : SourceNoAlloc.Only loop := by
    simp [loop,loopBody,condition,advance,branch,test,returnSentinel,SourceNoAlloc.Only,SourcePure.CallFree]
  have frame := SourceArrayFrame.exec_frame run writes noalloc h.well bindings
  simpa [SourceArrayFrame.writes,localWrites,scalarPointer] using frame

theorem loop_unique {F : Type} (context : Context F) : CompareSource.Unique context loop := by
  apply CompareSource.while_unique
  · simp [condition,SourcePure.CallFree]
  · apply CompareSource.block_unique
    intro stmt member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl
    · exact CompareSource.return_branch_unique test sentinel (by simp [test,SourcePure.CallFree])
    · exact fun first second => PureDeterminism.simple_unique (by simp [advance,PureDeterminism.Simple,SourcePure.CallFree]) first second

#print axioms advance_execution
#print axioms body_execution
#print axioms loop_execution
#print axioms loop_frame
#print axioms loop_unique
end RH080Next.FFTPV.ConvertBoundSource
