/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroLoop
import GoldbachDirect.SourceBindings
import GoldbachDirect.SourceArrayFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ZeroFrame
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

inductive Var where | a | n | j deriving DecidableEq

def name : Var → String | .a=>"a" | .n=>"n" | .j=>"j"
def type : Var → CType | .a=>.pointer .u64 | .n|.j=>.u64
def value (object length j : Nat) : Var → Value
  | .a=>.pointer (wordPointer object 0)
  | .n=>.integer (integer64 length)
  | .j=>.integer (integer64 j)

/-- Actual typed source bindings and host allocation. Unrelated caller objects,
foreign state, object identities and scope numbers are arbitrary. -/
structure View {F : Type} (state : State F) (object length owner : Nat)
    (ids : Var → Nat) (j : Nat) : Prop where
  host : state.mode=.host
  buffer : state.objects object=some (zeroPrefixObject length j)
  locals : Locals state name type ids owner (value object length j)
  separate : ∀v,object≠ids v
  well : WellScoped state
  active : j≤length
  fits : length<2^64

theorem View.enter {F : Type} {state : State F} {object length owner j : Nat}
    {ids : Var→Nat} (h : View state object length owner ids j) :
    View state.enterScope object length owner ids j :=
  ⟨h.host,h.buffer,h.locals.enter,h.separate,wellScoped_enter h.well,h.active,h.fits⟩

private theorem word_storable (n : Nat) (hn : n<2^64) :
    Storable .u64 (.integer (integer64 n)) := by
  have hb : (Value.integer (integer64 n)).byteSize=8 := stored_u64_width n
  exact ⟨by rw [hb]; rfl,by rw [hb]; decide,convert64 n hn⟩

private theorem locals_store_outside {F I : Type} {before after : State F}
    {names : I→String} {types : I→CType} {ids : I→Nat} {owner : Nat} {values : I→Value}
    (h : Locals before names types ids owner values) {p : Pointer} {v : Value}
    (different : ∀i,ids i≠p.object) (stored : before.store p v=some after) :
    Locals after names types ids owner values := by
  obtain ⟨env,mode,scope,nextScope,nextObject,outside⟩ := store_frame stored
  refine ⟨?_,?_,h.distinct,?_⟩
  · intro i
    rw [env]
    exact h.lookup i
  · intro i
    refine ⟨(h.slots i).storable,?_⟩
    rw [outside (ids i) (different i)]
    exact (h.slots i).object
  · rw [nextScope]
    exact h.bound

private theorem slot_store_exists {F : Type} {state : State F} {id owner : Nat}
    {type : CType} {old : Value} (h : Slot state id owner type old)
    (v : Value) (hv : Storable type v) :
    ∃after,state.store (scalarPointer id type) v=some after := by
  obtain ⟨oldType,present⟩ := h
  have hsame : old.byteSize=v.byteSize := Option.some.inj (oldType.typeWidth.symm.trans hv.typeWidth)
  rw [hsame] at present
  simp [State.store,scalarPointer,present,scalarObject,State.accessible,hv.typeWidth,hv.converted]


/-- Actual two source assignments in an arbitrary caller heap. -/
theorem contents_execution {F : Type} (context : Context F) {before : State F}
    {object length owner j : Nat} {ids : Var→Nat}
    (h : View before object length owner ids j) (hj : j<length) :
    ∃after,ExecList context before [zeroStoreStmt,ZeroLoop.increment] .normal after ∧
      View after object length owner ids (j+1) := by
  let middle : State F := {before with objects := fun key => if key = object then some (zeroPrefixObject length (j+1)) else before.objects key}
  have writeBuffer : before.store (wordPointer object j) (.integer (integer64 0))=some middle :=
    zeroPrefix_store h.host h.buffer hj
  have bufferRun : Exec context before zeroStoreStmt .normal middle :=
    .assign (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
      (.index (.variable (h.locals.lookup Var.a) (h.locals.read Var.a))
        (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
        (zero_array_pointer_add h.host h.buffer hj)) writeBuffer
  have lm : Locals middle name type ids owner (value object length j) :=
    locals_store_outside h.locals (fun v=>Ne.symm (h.separate v)) writeBuffer
  have fits : j+1<2^64 := lt_of_le_of_lt (by omega) h.fits
  obtain ⟨after,writeCounter⟩ := slot_store_exists (lm.slots Var.j)
    (.integer (integer64 (j+1))) (word_storable (j+1) fits)
  have counterRun : Exec context middle ZeroLoop.increment .normal after := by
    apply Exec.assign (value:=.integer (integer64 (j+1)))
      (Eval.paren (Eval.binaryLR (.variable (lm.lookup Var.j) (lm.read Var.j))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [value,binary,binary64_add j 1 (by omega) (by norm_num) fits,Option.map_some])))
      (.variable (lm.lookup Var.j))
    exact writeCounter
  have la := lm.store Var.j (.integer (integer64 (j+1)))
    (word_storable (j+1) fits) writeCounter
  have hvalues : Function.update (value object length j) Var.j (.integer (integer64 (j+1)))=
      value object length (j+1) := by
    funext v
    cases v <;> simp [value,Function.update]
  rw [hvalues] at la
  obtain ⟨env,mode,scope,ns,no,outside⟩ := store_frame writeCounter
  refine ⟨after,.cons bufferRun (.cons counterRun .nil),?_,?_,la,h.separate,?_,by omega,h.fits⟩
  · exact mode.trans h.host
  · rw [outside object (h.separate Var.j)]
    simp [middle]
  · exact wellScoped_store (wellScoped_store h.well writeBuffer) writeCounter


/-- Fresh block entry/exit preserves the caller's actual automatic slots and
unrelated objects; no fixed object IDs or scope numbers are used. -/
theorem block_execution {F : Type} (context : Context F) {before : State F}
    {object length owner j : Nat} {ids : Var→Nat}
    (h : View before object length owner ids j) (hj : j<length) :
    ∃after,Exec context before ZeroLoop.loopBody .normal after ∧
      View after object length owner ids (j+1) := by
  obtain ⟨middle,run,hm⟩ := contents_execution context h.enter hj
  let after : State F :=
    {middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have blockRun : Exec context before ZeroLoop.loopBody .normal after :=
    .block (by rfl) run (by rfl)
  have effect := SourceNoAlloc.exec_effect blockRun
    (by simp [ZeroLoop.loopBody,ZeroLoop.increment,zeroStoreStmt,
      SourceNoAlloc.Only,SourcePure.CallFree]) h.well
  have different : before.nextScope≠owner := by have ho:=h.locals.bound; omega
  have la := hm.locals.leave different before.environment h.locals.lookup before.scope
  refine ⟨after,blockRun,hm.host,?_,la,hm.separate,effect.well,hm.active,hm.fits⟩
  change (middle.objects object).map _=some (zeroPrefixObject length (j+1))
  rw [hm.buffer]
  simp [zeroPrefixObject]


private theorem binary64_lt (j n : Nat) (hj : j<2^64) (hn : n<2^64) :
    Integer.binary .lt (integer64 j) (integer64 n)=some (.boolean (decide (j<n))) := by
  change some (Integer.boolean ((Integer.cast .u64 (j:Int)).toInt<
    (Integer.cast .u64 (n:Int)).toInt))=_
  rw [cast64_exact j hj,cast64_exact n hn,integer64_toInt,integer64_toInt]
  congr 2
  simp

private theorem condition_eval {F : Type} (context : Context F) {before : State F}
    {object length owner j : Nat} {ids : Var→Nat}
    (h : View before object length owner ids j) :
    Eval context before ZeroLoop.condition (.integer (.boolean (decide (j<length)))) before := by
  exact .binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
    (.variable (h.locals.lookup Var.n) (h.locals.read Var.n))
    (by simp only [value,binary,binary64_lt j length (lt_of_le_of_lt h.active h.fits) h.fits,
      Option.map_some])

/-- Complete actual loop execution in an arbitrary well-scoped caller frame.
All iteration counts are covered by induction, with no native execution axiom. -/
theorem loop_execution {F : Type} (context : Context F) (steps : Nat)
    {before : State F} {object length owner j : Nat} {ids : Var→Nat}
    (h : View before object length owner ids j) (remaining : j+steps=length) :
    ∃after,Exec context before ZeroLoop.loop .normal after ∧
      View after object length owner ids length := by
  induction steps generalizing before j with
  | zero =>
    have he : j=length := by omega
    subst j
    refine ⟨before,?_,h⟩
    exact .whileFalse (condition_eval context h)
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed])
  | succ steps ih =>
    have hj : j<length := by omega
    obtain ⟨middle,first,hm⟩ := block_execution context h hj
    obtain ⟨after,rest,ha⟩ := ih hm (by omega)
    refine ⟨after,Exec.whileNext (condition_eval context h) ?_ first rest,ha⟩
    simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj]

/-- Actual typed zero output obtained from a byte-prefix entry frame; all other
caller data and scope numbers remain unrestricted by this theorem. -/
theorem loop_zero_output {F : Type} (context : Context F) {before : State F}
    {object length owner j : Nat} {ids : Var→Nat}
    (h : View before object length owner ids j) :
    ∃after,Exec context before ZeroLoop.loop .normal after ∧
      View after object length owner ids length ∧
      WordArrayRep after object length (fun _=>0) := by
  obtain ⟨after,run,ha⟩ := loop_execution context (length-j) h (by have ha:=h.active; omega)
  refine ⟨after,run,ha,ha.host,?_,fun i hi=>by norm_num⟩
  simpa only [zeroPrefix_full] using ha.buffer


def localWrites (ids : Var→Nat) : List (String×Pointer) :=
  [("j",scalarPointer (ids Var.j) .u64)]
def arrayWrites (ids : Var→Nat) (object : Nat) : List SourceArrayFrame.ArrayBinding :=
  [⟨"a",scalarPointer (ids Var.a) (.pointer .u64),wordPointer object 0⟩]

private theorem view_bindings {F : Type} {before : State F}
    {object length owner j : Nat} {ids : Var→Nat}
    (h : View before object length owner ids j) :
    SourceArrayFrame.Bindings before (localWrites ids) (arrayWrites ids object) := by
  constructor
  · intro actualName pointer member
    simp only [localWrites,List.mem_singleton,Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩
    exact h.locals.lookup Var.j
  · intro item member
    simp only [arrayWrites,List.mem_singleton] at member
    subst item
    exact ⟨h.locals.lookup Var.a,h.locals.read Var.a⟩
  · intro item member
    simp only [arrayWrites,List.mem_singleton] at member
    subst item
    have hd : ids Var.a≠ids Var.j := by intro he; have hh:=h.locals.distinct he; cases hh
    have hb : ids Var.a≠object := Ne.symm (h.separate Var.a)
    simpa [SourceArrayFrame.writes,localWrites,arrayWrites,scalarPointer,wordPointer] using And.intro hd hb

private theorem loop_writes_only (ids : Var→Nat) (object : Nat) :
    SourceArrayFrame.Only (localWrites ids) (arrayWrites ids object) ZeroLoop.loop := by
  simp [ZeroLoop.loop,ZeroLoop.loopBody,ZeroLoop.increment,zeroStoreStmt,
    SourceArrayFrame.Only,SourceArrayFrame.Writable,localWrites,arrayWrites]

private theorem loop_no_alloc : SourceNoAlloc.Only ZeroLoop.loop := by
  simp [ZeroLoop.loop,ZeroLoop.condition,ZeroLoop.loopBody,ZeroLoop.increment,zeroStoreStmt,
    SourceNoAlloc.Only,SourcePure.CallFree]

/-- Every execution of this actual source loop preserves all caller objects
outside the data buffer and the genuine automatic j slot. -/
theorem loop_frame {F : Type} {context : Context F} {before after : State F}
    {object length owner j : Nat} {ids : Var→Nat}
    (h : View before object length owner ids j) {flow : Flow}
    (run : Exec context before ZeroLoop.loop flow after) :
    ScanFrame.Frame before after [ids Var.j,object] := by
  have hf := SourceArrayFrame.exec_frame run (loop_writes_only ids object)
    loop_no_alloc h.well (view_bindings h)
  simpa [SourceArrayFrame.writes,localWrites,arrayWrites,scalarPointer,wordPointer] using hf

/-- Actual complete loop, typed output and arbitrary caller-object frame. -/
theorem loop_zero_output_frame {F : Type} (context : Context F) {before : State F}
    {object length owner j : Nat} {ids : Var→Nat}
    (h : View before object length owner ids j) :
    ∃after,Exec context before ZeroLoop.loop .normal after ∧
      View after object length owner ids length ∧
      WordArrayRep after object length (fun _=>0) ∧
      ScanFrame.Frame before after [ids Var.j,object] := by
  obtain ⟨after,run,ha,words⟩ := loop_zero_output context h
  exact ⟨after,run,ha,words,loop_frame h run⟩

#print axioms loop_frame
#print axioms loop_zero_output_frame

#print axioms loop_execution
#print axioms loop_zero_output

#print axioms block_execution

#print axioms contents_execution

#print axioms View.enter
#print axioms locals_store_outside
#print axioms slot_store_exists
end RH080Next.FFTPV.ZeroFrame
