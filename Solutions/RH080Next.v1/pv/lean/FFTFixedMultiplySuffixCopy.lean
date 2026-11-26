/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixLost
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner

inductive CVar where | out | work | i deriving DecidableEq
def copyName : CVar → String | .out => "out" | .work => "work" | .i => "i"
def copyType : CVar → CType | .out | .work => .pointer .u64 | .i => .u64
def copyValues (outObject outStart workObject workStart j : Nat) : CVar → Value
  | .out => .pointer (wordPointer outObject outStart)
  | .work => .pointer (wordPointer workObject workStart)
  | .i => .integer (integer64 j)
def copied (old scratch : Nat → Nat) (outStart j : Nat) : Nat → Nat :=
  CopyLoop.prefixData old (fun k => scratch (k+4)) outStart j

structure CopyView {F : Type} (state : State F)
    (outObject outSize outStart workObject workSize workStart : Nat)
    (ids owners : CVar → Nat) (old scratch : Nat → Nat) (j : Nat) : Prop where
  output : WordArrayRep state outObject outSize (copied old scratch outStart j)
  work : ∃data, WordArrayRep state workObject workSize data ∧ ∀k, k<10 → data (workStart+k)=scratch k
  locals : Bindings state copyName copyType ids owners (copyValues outObject outStart workObject workStart j)
  separate : ∀x, outObject≠ids x ∧ workObject≠ids x
  shape : workObject=outObject → workSize=outSize
  disjoint : outObject≠workObject ∨ outStart+6≤workStart ∨ workStart+10≤outStart
  outBound : outStart+6≤outSize
  workBound : workStart+10≤workSize
  well : WellScoped state
  active : j≤5

theorem CopyView.enter {F : Type} {state : State F}
    {outObject outSize outStart workObject workSize workStart j : Nat}
    {ids owners : CVar → Nat} {old scratch : Nat → Nat}
    (h : CopyView state outObject outSize outStart workObject workSize workStart ids owners old scratch j) :
    CopyView state.enterScope outObject outSize outStart workObject workSize workStart ids owners old scratch j := by
  obtain ⟨data,rep,vals⟩:=h.work
  exact ⟨h.output,⟨data,rep,vals⟩,h.locals.enter,h.separate,h.shape,h.disjoint,h.outBound,h.workBound,wellScoped_enter h.well,h.active⟩

private theorem slot_store_exists {F : Type} {state : State F} {id owner : Nat}
    {ctype : CType} {old : Value} (h : Slot state id owner ctype old)
    (v : Value) (hv : Storable ctype v) : ∃after, state.store (scalarPointer id ctype) v=some after := by
  obtain ⟨ht,present⟩:=h
  have same : old.byteSize=v.byteSize:=Option.some.inj (ht.typeWidth.symm.trans hv.typeWidth)
  rw [same] at present
  simp [State.store,scalarPointer,present,scalarObject,State.accessible,hv.typeWidth,hv.converted]

/-- One actual retained-digit store; even one shared allocation keeps all ten
workspace words unchanged because the true source ranges are disjoint. -/
theorem copy_store_execution {F : Type} (context : Context F) {before : State F}
    {outObject outSize outStart workObject workSize workStart j : Nat}
    {ids owners : CVar → Nat} {old scratch : Nat → Nat}
    (h : CopyView before outObject outSize outStart workObject workSize workStart ids owners old scratch j)
    (hj : j<5) :
    ∃middle, Exec context before copyStore .normal middle ∧
      WordArrayRep middle outObject outSize (copied old scratch outStart (j+1)) ∧
      (∃data,WordArrayRep middle workObject workSize data ∧ ∀k,k<10 → data (workStart+k)=scratch k) ∧
      Bindings middle copyName copyType ids owners (copyValues outObject outStart workObject workStart j) ∧ WellScoped middle := by
  obtain ⟨data,rep,vals⟩:=h.work
  have hi : workStart+(j+4)<workSize := by have hb:=h.workBound;omega
  have ho : outStart+j<outSize := by have hb:=h.outBound;omega
  have inputFit : scratch (j+4)<2^64 := by rw [←vals (j+4) (by omega)];exact rep.2.2 _ hi
  obtain ⟨middle,written,outRep⟩:=word_store_with_rep h.output ho inputFit
  have outRep' : WordArrayRep middle outObject outSize (copied old scratch outStart (j+1)):=by
    simpa only [copied,CopyLoop.prefixData_step] using outRep
  have inputRead : before.load (wordPointer workObject (workStart+(j+4)))=some (.integer (integer64 (scratch (j+4)))):=by
    rw [←vals (j+4) (by omega)];exact word_load rep hi
  have indexRun : Eval context before (.paren (.binary .add (v "i") (lit 4))) (.integer (integer64 (j+4))) before :=
    .paren (.binaryLR (.variable (h.locals.lookup CVar.i) (h.locals.read CVar.i))
      (.literal (.integer 4 "ULL") _ (.integer (integer64 4)) (by rfl))
      (by simp only [copyValues,binary,binary64_add j 4 (by omega) (by norm_num) (by omega),Option.map_some]))
  have run : Exec context before copyStore .normal middle :=
    .assign (.load (.index (.variable (h.locals.lookup CVar.work) (h.locals.read CVar.work)) indexRun
      (slice_pointer_add rep hi)) inputRead)
      (.index (.variable (h.locals.lookup CVar.out) (h.locals.read CVar.out))
        (.variable (h.locals.lookup CVar.i) (h.locals.read CVar.i)) (slice_pointer_add h.output ho)) written
  have source : ∃data,WordArrayRep middle workObject workSize data ∧ ∀k,k<10 → data (workStart+k)=scratch k := by
    by_cases same : workObject=outObject
    · have sizeEq:=h.shape same
      subst workObject;subst workSize
      refine ⟨copied old scratch outStart (j+1),outRep',?_⟩
      intro k hk
      have bound : workStart+k<outSize := by have hb:=h.workBound;omega
      have previous : copied old scratch outStart j (workStart+k)=scratch k :=
        (word_data_unique h.output rep _ bound).trans (vals k hk)
      have different : workStart+k≠outStart+j := by
        rcases h.disjoint with no | left | right
        · exact False.elim (no rfl)
        · omega
        · omega
      rw [copied,←CopyLoop.prefixData_step,Function.update_of_ne different]
      exact previous
    · obtain ⟨env,mode,scope,ns,no,outside⟩:=SourceLocals.store_frame written
      exact ⟨data,⟨mode.trans rep.1,(outside workObject same).trans rep.2.1,rep.2.2⟩,vals⟩
  exact ⟨middle,run,outRep',source,h.locals.store_other (fun x=>(h.separate x).1.symm) written,wellScoped_store h.well written⟩

theorem copy_contents_execution {F : Type} (context : Context F) {before : State F}
    {outObject outSize outStart workObject workSize workStart j : Nat}
    {ids owners : CVar → Nat} {old scratch : Nat → Nat}
    (h : CopyView before outObject outSize outStart workObject workSize workStart ids owners old scratch j)
    (hj : j<5) :
    ∃after,ExecList context before [copyStore,increment] .normal after ∧
      CopyView after outObject outSize outStart workObject workSize workStart ids owners old scratch (j+1) := by
  obtain ⟨middle,copyRun,outRep,source,lm,wm⟩:=copy_store_execution context h hj
  obtain ⟨after,written⟩:=slot_store_exists (lm.slots CVar.i) (.integer (integer64 (j+1))) (ZeroFrame.u64_storable _ (by omega))
  have incRun : Exec context middle increment .normal after := by
    apply Exec.assign (value:=.integer (integer64 (j+1)))
      (.paren (.binaryLR (.variable (lm.lookup CVar.i) (lm.read CVar.i))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [copyValues,binary,binary64_add j 1 (by omega) (by norm_num) (by omega),Option.map_some])))
      (.variable (lm.lookup CVar.i))
    exact written
  have la:=lm.store CVar.i (.integer (integer64 (j+1))) (ZeroFrame.u64_storable _ (by omega)) written
  have eqValues : Function.update (copyValues outObject outStart workObject workStart j) CVar.i (.integer (integer64 (j+1)))=
      copyValues outObject outStart workObject workStart (j+1):=by funext x;cases x <;> simp [copyValues,Function.update]
  rw [eqValues] at la
  obtain ⟨env,mode,scope,ns,no,outside⟩:=SourceLocals.store_frame written
  obtain ⟨data,rep,vals⟩:=source
  exact ⟨after,.cons copyRun (.cons incRun .nil),
    ⟨mode.trans outRep.1,(outside outObject (h.separate CVar.i).1).trans outRep.2.1,outRep.2.2⟩,
    ⟨data,⟨mode.trans rep.1,(outside workObject (h.separate CVar.i).2).trans rep.2.1,rep.2.2⟩,vals⟩,
    la,h.separate,h.shape,h.disjoint,h.outBound,h.workBound,wellScoped_store wm written,by omega⟩

private theorem wordArray_leave {F : Type} {state : State F} {object size scope restore : Nat}
    {environment : List (String×Pointer)} {data : Nat→Nat}(h:WordArrayRep state object size data):
    WordArrayRep {state.leaveScope scope environment with scope:=restore} object size data:=by
  refine ⟨h.1,?_,h.2.2⟩
  change (state.objects object).map _=some _
  rw [h.2.1]
  simp [wordObject]

theorem copy_block_execution {F : Type} (context : Context F) {before : State F}
    {outObject outSize outStart workObject workSize workStart j : Nat}
    {ids owners : CVar → Nat} {old scratch : Nat → Nat}
    (h : CopyView before outObject outSize outStart workObject workSize workStart ids owners old scratch j)
    (hj : j<5) :
    ∃after,Exec context before copyBody .normal after ∧ CopyView after outObject outSize outStart workObject workSize workStart ids owners old scratch (j+1) := by
  obtain ⟨middle,run,hm⟩:=copy_contents_execution context h.enter hj
  let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have blockRun : Exec context before copyBody .normal after:=.block (by rfl) run (by rfl)
  have effect:=SourceNoAlloc.exec_effect blockRun
    (by simp [copyBody,copyStore,increment,v,lit,SourceNoAlloc.Only,SourcePure.CallFree]) h.well
  have different : ∀x,before.nextScope≠owners x:=by intro x;have ho:=h.locals.bound x;omega
  have la:=hm.locals.leave (restore:=before.scope) different before.environment h.locals.lookup
  obtain ⟨data,rep,vals⟩:=hm.work
  exact ⟨after,blockRun,wordArray_leave (environment:=before.environment) (restore:=before.scope) hm.output,
    ⟨data,wordArray_leave (environment:=before.environment) (restore:=before.scope) rep,vals⟩,
    la,hm.separate,hm.shape,hm.disjoint,hm.outBound,hm.workBound,effect.well,hm.active⟩

private theorem copy_condition_execution {F : Type}(context:Context F){before:State F}
    {outObject outSize outStart workObject workSize workStart j:Nat}{ids owners:CVar→Nat}{old scratch:Nat→Nat}
    (h:CopyView before outObject outSize outStart workObject workSize workStart ids owners old scratch j):
    Eval context before copyCondition (.integer (.boolean (decide (j<5)))) before:=by
  exact .binaryLR (.variable (h.locals.lookup CVar.i) (h.locals.read CVar.i))
    (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
    (by simp only [copyValues,binary,binary64_lt j 5 (by have a:=h.active;omega) (by norm_num),Option.map_some])

theorem copy_loop_execution {F:Type}(context:Context F) (steps:Nat){before:State F}
    {outObject outSize outStart workObject workSize workStart j:Nat}{ids owners:CVar→Nat}{old scratch:Nat→Nat}
    (h:CopyView before outObject outSize outStart workObject workSize workStart ids owners old scratch j)
    (remaining:j+steps=5):
    ∃after,Exec context before copyLoop .normal after ∧ CopyView after outObject outSize outStart workObject workSize workStart ids owners old scratch 5:=by
  induction steps generalizing before j with
  | zero=>
    have equal:j=5:=by omega
    subst j
    exact ⟨before,.whileFalse (copy_condition_execution context h) (by decide),h⟩
  | succ steps ih=>
    have hj:j<5:=by omega
    obtain ⟨middle,first,hm⟩:=copy_block_execution context h hj
    obtain ⟨after,rest,ha⟩:=ih hm (by omega)
    refine ⟨after,.whileNext (copy_condition_execution context h) ?_ first rest,ha⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj]

def copyWrites (ids : CVar → Nat) : List (String × Pointer) :=
  [("i", scalarPointer (ids CVar.i) .u64)]
def copyArrays (ids : CVar → Nat) (object start : Nat) : List SourceArrayFrame.ArrayBinding :=
  [⟨"out", scalarPointer (ids CVar.out) (.pointer .u64), wordPointer object start⟩]

theorem copy_loop_frame {F : Type} {context : Context F} {before after : State F}
    {outObject outSize outStart workObject workSize workStart j : Nat}
    {ids owners : CVar → Nat} {old scratch : Nat → Nat}
    (h : CopyView before outObject outSize outStart workObject workSize workStart ids owners old scratch j)
    {flow : Flow} (run : Exec context before copyLoop flow after) :
    ScanFrame.Frame before after [ids CVar.i, outObject] := by
  have bindings : SourceArrayFrame.Bindings before (copyWrites ids) (copyArrays ids outObject outStart) := by
    constructor
    · intro actualName pointer member
      simp only [copyWrites, List.mem_singleton, Prod.mk.injEq] at member
      rcases member with ⟨rfl,rfl⟩
      exact h.locals.lookup CVar.i
    · intro item member
      simp only [copyArrays, List.mem_singleton] at member
      subst item
      exact ⟨h.locals.lookup CVar.out,h.locals.read CVar.out⟩
    · intro item member
      simp only [copyArrays, List.mem_singleton] at member
      subst item
      have different : ids CVar.out ≠ ids CVar.i := by intro eq;have bad:=h.locals.distinct eq;cases bad
      simpa [SourceArrayFrame.writes,copyWrites,copyArrays,scalarPointer,wordPointer] using
        And.intro different (h.separate CVar.out).1.symm
  have only : SourceArrayFrame.Only (copyWrites ids) (copyArrays ids outObject outStart) copyLoop := by
    simp [copyLoop,copyBody,copyStore,increment,v,lit,SourceArrayFrame.Only,SourceArrayFrame.Writable,copyWrites,copyArrays]
  have noAlloc : SourceNoAlloc.Only copyLoop := by
    simp [copyLoop,copyCondition,copyBody,copyStore,increment,v,lit,SourceNoAlloc.Only,SourcePure.CallFree]
  have frame := SourceArrayFrame.exec_frame run only noAlloc h.well bindings
  simpa [SourceArrayFrame.writes,copyWrites,copyArrays,scalarPointer,wordPointer] using frame

theorem copy_loop_unique {F : Type} (context : Context F) : CompareSource.Unique context copyLoop := by
  apply CompareSource.while_unique (by simp [copyCondition,v,lit,SourcePure.CallFree])
  intro before a b fa fb first second
  exact PureDeterminism.block_unique
    (by simp [copyBody,copyStore,increment,v,lit,PureDeterminism.Simple,SourcePure.CallFree]) first second

/-- Every permitted source execution yields the same five copied actual digits
and preserves every caller allocation outside destination and local counter. -/
theorem every_copy_loop {F : Type} {context : Context F} {before after : State F}
    {outObject outSize outStart workObject workSize workStart j : Nat}
    {ids owners : CVar → Nat} {old scratch : Nat → Nat}
    (h : CopyView before outObject outSize outStart workObject workSize workStart ids owners old scratch j)
    {flow : Flow} (run : Exec context before copyLoop flow after) :
    flow = .normal ∧ CopyView after outObject outSize outStart workObject workSize workStart ids owners old scratch 5 ∧
      ScanFrame.Frame before after [ids CVar.i,outObject] := by
  obtain ⟨canonical,known,view⟩ := copy_loop_execution context (5-j) h (by have hj:=h.active;omega)
  obtain ⟨flowEq,stateEq⟩ := copy_loop_unique context run known
  cases stateEq
  exact ⟨flowEq,view,copy_loop_frame h run⟩
#print axioms every_copy_loop

#print axioms copy_store_execution
#print axioms copy_loop_execution
end RH080Next.FFTPV.MultiplySuffix
