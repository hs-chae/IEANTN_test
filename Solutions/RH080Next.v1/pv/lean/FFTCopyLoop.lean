/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroParameters
import FFTWordSlices
import FFTRecursiveAST
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CopyLoop
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- Exact output contents after j source assignments; the source slice itself
is kept fixed by the proved disjoint-range precondition. -/
def prefixData (old input : Nat → Nat) (start j index : Nat) : Nat :=
  if start  ≤  index ∧ index < start+j then input (index-start) else old index

theorem prefixData_zero (old input : Nat → Nat) (start : Nat) :
    prefixData old input start 0=old := by
  funext i
  simp [prefixData]

theorem prefixData_step (old input : Nat → Nat) (start j : Nat) :
    Function.update (prefixData old input start j) (start+j) (input j)=
      prefixData old input start (j+1) := by
  funext i
  by_cases he : i=start+j
  · subst i
    simp [prefixData,Function.update]
  · by_cases hi : start  ≤  i ∧ i < start+j
    · simp [prefixData,Function.update_of_ne he,hi,show start  ≤  i ∧ i < start+(j+1) by omega]
    · simp [prefixData,Function.update_of_ne he,hi,
        show ¬(start  ≤  i ∧ i < start+(j+1)) by omega]

def storeStmt : Stmt := .assign (.index (.variable "out") (.variable "j"))
  (.index (.variable "in") (.variable "j"))
def condition : Expr := ZeroLoop.condition
def increment : Stmt := ZeroLoop.increment
def loopBody : Stmt := .block [storeStmt,increment]
def loop : Stmt := .whileLoop condition loopBody

theorem recursive_body_actual : FFTRecursivePV.copy_words_ast.body=
    .block [.declare .u64 "j" (some (.literal (.integer 0 "ULL"))),
      loop,.returnValue (some (.literal (.integer 0 "ULL")))] := by rfl

theorem iterative_body_actual : copy_words_ast.body=
    .block [.declare .u64 "j" (some (.literal (.integer 0 "ULL"))),
      loop,.returnValue (some (.literal (.integer 0 "ULL")))] := by rfl

inductive Var where | output | input | n | j deriving DecidableEq

def name : Var → String | .output=>"out" | .input=>"in" | .n=>"n" | .j=>"j"
def type : Var → CType | .output|.input=>.pointer .u64 | .n|.j=>.u64
def value (outObject outStart inObject inStart length j : Nat) : Var → Value
  | .output=>.pointer (wordPointer outObject outStart)
  | .input=>.pointer (wordPointer inObject inStart)
  | .n=>.integer (integer64 length)
  | .j=>.integer (integer64 j)

/-- Arbitrary well-scoped caller frame. Separate allocations and disjoint
slices of the same allocation are both allowed. The input representation is
actual typed memory and is preserved; it is never a successful-effects oracle. -/
structure View {F : Type} (state : State F)
    (outObject outLength outStart inObject inLength inStart length owner : Nat)
    (ids : Var → Nat) (old input : Nat → Nat) (j : Nat) : Prop where
  host : state.mode=.host
  output : WordArrayRep state outObject outLength (prefixData old input outStart j)
  source : ∃data,WordArrayRep state inObject inLength data ∧
    ∀ i,i < length → data (inStart+i)=input i
  locals : Locals state name type ids owner (value outObject outStart inObject inStart length j)
  separate : ∀v,outObject≠ids v ∧ inObject≠ids v
  shape : inObject=outObject → inLength=outLength
  ranges : outObject≠inObject ∨ outStart=inStart ∨ outStart+length  ≤  inStart ∨ inStart+length  ≤  outStart
  outBound : outStart+length  ≤  outLength
  inBound : inStart+length  ≤  inLength
  well : WellScoped state
  active : j  ≤  length
  fits : length < 2^64

/-- Array indexing is valid at the actual source slice offset. -/
theorem array_pointer_add {F : Type} {state : State F} {object size start i : Nat}
    {data : Nat → Nat} (h : WordArrayRep state object size data) (hi : start+i < size) :
    state.pointerAdd (wordPointer object start) (integer64 i).toInt=
      some (wordPointer object (start+i)) := by
  exact slice_pointer_add h hi

private theorem updated_word_fits (old : Nat → Nat) (index value size : Nat)
    (fit : ∀i,i < size → old i < 2^64) (hv : value < 2^64) :
    ∀i,i < size → Function.update old index value i < 2^64 := by
  intro i hi
  by_cases h : i=index
  · subst i; simpa using hv
  · simpa [Function.update_of_ne h] using fit i hi

theorem View.enter {F : Type} {state : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat}
    (h : View state outObject outLength outStart inObject inLength inStart length owner ids old input j) :
    View state.enterScope outObject outLength outStart inObject inLength inStart length owner ids old input j := by
  obtain ⟨data,rep,values⟩ := h.source
  exact ⟨h.host,h.output,⟨data,rep,values⟩,h.locals.enter,h.separate,h.shape,h.ranges,
    h.outBound,h.inBound,wellScoped_enter h.well,h.active,h.fits⟩

private theorem locals_store_outside {F I : Type} {before after : State F}
    {names : I → String} {types : I → CType} {ids : I → Nat} {owner : Nat} {values : I → Value}
    (h : Locals before names types ids owner values) {p : Pointer} {v : Value}
    (different : ∀i,ids i≠p.object) (stored : before.store p v=some after) :
    Locals after names types ids owner values := by
  obtain ⟨env,mode,scope,nextScope,nextObject,outside⟩ := store_frame stored
  refine ⟨?_,?_,h.distinct,?_⟩
  · intro i; rw [env]; exact h.lookup i
  · intro i
    exact ⟨(h.slots i).storable,by rw [outside (ids i) (different i)]; exact (h.slots i).object⟩
  · rw [nextScope]; exact h.bound

private theorem slot_store_exists {F : Type} {state : State F} {id owner : Nat}
    {ctype : CType} {oldValue : Value} (h : Slot state id owner ctype oldValue)
    (v : Value) (hv : Storable ctype v) : ∃after,state.store (scalarPointer id ctype) v=some after := by
  obtain ⟨oldType,present⟩ := h
  have hsame : oldValue.byteSize=v.byteSize := Option.some.inj (oldType.typeWidth.symm.trans hv.typeWidth)
  rw [hsame] at present
  simp [State.store,scalarPointer,present,scalarObject,State.accessible,hv.typeWidth,hv.converted]

/-- One genuine source array assignment preserves all input slice values,
including disjoint or identical slices within one actual allocation. -/
theorem store_execution {F : Type} (context : Context F) {before : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j)
    (hj : j < length) :
    ∃middle,Exec context before storeStmt .normal middle ∧
      WordArrayRep middle outObject outLength (prefixData old input outStart (j+1)) ∧
      (∃data,WordArrayRep middle inObject inLength data ∧ ∀i,i < length → data (inStart+i)=input i) ∧
      Locals middle name type ids owner (value outObject outStart inObject inStart length j) ∧
      WellScoped middle := by
  obtain ⟨data,inRep,inValues⟩ := h.source
  have hiIn : inStart+j < inLength := by have hb:=h.inBound; omega
  have hiOut : outStart+j < outLength := by have hb:=h.outBound; omega
  have hfit : input j < 2^64 := by rw [← inValues j hj]; exact inRep.2.2 _ hiIn
  let middle : State F := {before with objects := fun key => if key = outObject then some (wordObject outLength (prefixData old input outStart (j+1))) else before.objects key}
  have written : before.store (wordPointer outObject (outStart+j)) (.integer (integer64 (input j)))=some middle := by
    have hw := word_store h.output hiOut hfit
    simpa only [prefixData_step] using hw
  have outRep : WordArrayRep middle outObject outLength (prefixData old input outStart (j+1)) := by
    refine ⟨h.host,by simp [middle],?_⟩
    rw [← prefixData_step]
    exact updated_word_fits _ _ _ _ h.output.2.2 hfit
  have inLoad : before.load (wordPointer inObject (inStart+j))=some (.integer (integer64 (input j))) := by
    rw [← inValues j hj]
    exact word_load inRep hiIn
  have run : Exec context before storeStmt .normal middle := by
    apply Exec.assign
      (Eval.load (.index (.variable (h.locals.lookup Var.input) (h.locals.read Var.input))
        (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
        (array_pointer_add inRep hiIn)) inLoad)
      (.index (.variable (h.locals.lookup Var.output) (h.locals.read Var.output))
        (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
        (array_pointer_add h.output hiOut))
    exact written
  have source : ∃data,WordArrayRep middle inObject inLength data ∧
      ∀i,i < length → data (inStart+i)=input i := by
    by_cases same : inObject=outObject
    · have sizeEq := h.shape same
      subst inObject
      subst inLength
      refine ⟨prefixData old input outStart (j+1),outRep,?_⟩
      intro i hi
      have hiIn' : inStart+i < outLength := by have hb:=h.inBound; omega
      have oldValue : prefixData old input outStart j (inStart+i)=input i :=
        (word_data_unique h.output inRep (inStart+i) hiIn').trans (inValues i hi)
      rw [← prefixData_step]
      by_cases collision : inStart+i=outStart+j
      · have ij : i=j := by
          rcases h.ranges with different | sameStart | beforeRange | afterRange
          · exact False.elim (different rfl)
          · omega
          · omega
          · omega
        subst i
        simp [collision, Function.update]
      · rw [Function.update_of_ne collision]
        exact oldValue
    · refine ⟨data,?_,inValues⟩
      exact ⟨h.host,by simpa [middle,same] using inRep.2.1,inRep.2.2⟩
  exact ⟨middle,run,outRep,source,
    locals_store_outside h.locals (fun v=>(h.separate v).1.symm) written,
    wellScoped_store h.well written⟩

/-- The two actual source assignments, with all typed stores and the copy
prefix invariant proved for arbitrary memory objects and slice offsets. -/
theorem contents_execution {F : Type} (context : Context F) {before : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j)
    (hj : j < length) :
    ∃after, ExecList context before [storeStmt, increment] .normal after ∧
      View after outObject outLength outStart inObject inLength inStart length owner ids old input (j+1) := by
  obtain ⟨middle, bufferRun, outRep, source, lm, wm⟩ := store_execution context h hj
  have fits : j+1 < 2^64 := lt_of_le_of_lt (by omega) h.fits
  obtain ⟨after, writeCounter⟩ := slot_store_exists (lm.slots Var.j)
    (.integer (integer64 (j+1))) (ZeroFrame.u64_storable (j+1) fits)
  have counterRun : Exec context middle increment .normal after := by
    apply Exec.assign (value := .integer (integer64 (j+1)))
      (Eval.paren (Eval.binaryLR (.variable (lm.lookup Var.j) (lm.read Var.j))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [value, binary, binary64_add j 1 (by omega) (by norm_num) fits, Option.map_some])))
      (.variable (lm.lookup Var.j))
    exact writeCounter
  have la := lm.store Var.j (.integer (integer64 (j+1)))
    (ZeroFrame.u64_storable (j+1) fits) writeCounter
  have hvalues : Function.update (value outObject outStart inObject inStart length j) Var.j
      (.integer (integer64 (j+1))) = value outObject outStart inObject inStart length (j+1) := by
    funext v
    cases v <;> simp [value, Function.update]
  rw [hvalues] at la
  obtain ⟨env, mode, scope, ns, no, outside⟩ := store_frame writeCounter
  have oa : WordArrayRep after outObject outLength (prefixData old input outStart (j+1)) :=
    ⟨mode.trans outRep.1, (outside outObject (h.separate Var.j).1).trans outRep.2.1, outRep.2.2⟩
  obtain ⟨data, rep, values⟩ := source
  have ia : WordArrayRep after inObject inLength data :=
    ⟨mode.trans rep.1, (outside inObject (h.separate Var.j).2).trans rep.2.1, rep.2.2⟩
  exact ⟨after, .cons bufferRun (.cons counterRun .nil), oa.1, oa, ⟨data, ia, values⟩,
    la, h.separate, h.shape, h.ranges, h.outBound, h.inBound,
    wellScoped_store wm writeCounter, by omega, h.fits⟩

private theorem wordArray_leave {F : Type} {state : State F} {object size scope restore : Nat}
    {environment : List (String × Pointer)} {data : Nat → Nat}
    (h : WordArrayRep state object size data) :
    WordArrayRep {state.leaveScope scope environment with scope := restore} object size data := by
  refine ⟨h.1, ?_, h.2.2⟩
  change (state.objects object).map _ = some (wordObject size data)
  rw [h.2.1]
  simp [wordObject]

/-- Source block scope entry and exit preserve actual caller slots and both
slice representations, including when both slices share an allocation. -/
theorem block_execution {F : Type} (context : Context F) {before : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j)
    (hj : j < length) :
    ∃after, Exec context before loopBody .normal after ∧
      View after outObject outLength outStart inObject inLength inStart length owner ids old input (j+1) := by
  obtain ⟨middle, run, hm⟩ := contents_execution context h.enter hj
  let after : State F := {middle.leaveScope before.nextScope before.environment with scope := before.scope}
  have blockRun : Exec context before loopBody .normal after := .block (by rfl) run (by rfl)
  have effect := SourceNoAlloc.exec_effect blockRun
    (by simp [loopBody, increment, ZeroLoop.increment, storeStmt, SourceNoAlloc.Only, SourcePure.CallFree]) h.well
  have different : before.nextScope ≠ owner := by have ho := h.locals.bound; omega
  have la := hm.locals.leave different before.environment h.locals.lookup before.scope
  obtain ⟨data, rep, values⟩ := hm.source
  exact ⟨after, blockRun, hm.host, wordArray_leave (environment := before.environment) (restore := before.scope) hm.output,
    ⟨data, wordArray_leave (environment := before.environment) (restore := before.scope) rep, values⟩, la, hm.separate, hm.shape, hm.ranges,
    hm.outBound, hm.inBound, effect.well, hm.active, hm.fits⟩

private theorem binary64_lt (j n : Nat) (hj : j < 2^64) (hn : n < 2^64) :
    Integer.binary .lt (integer64 j) (integer64 n) = some (.boolean (decide (j < n))) := by
  change some (Integer.boolean ((Integer.cast .u64 (j:Int)).toInt <
    (Integer.cast .u64 (n:Int)).toInt)) = _
  rw [cast64_exact j hj, cast64_exact n hn, integer64_toInt, integer64_toInt]
  congr 2
  simp

private theorem condition_eval {F : Type} (context : Context F) {before : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j) :
    Eval context before condition (.integer (.boolean (decide (j < length)))) before := by
  exact .binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
    (.variable (h.locals.lookup Var.n) (h.locals.read Var.n))
    (by simp only [value, binary, binary64_lt j length (lt_of_le_of_lt h.active h.fits) h.fits, Option.map_some])

/-- Complete actual source while loop, for every finite length and initial
prefix, without native computation or a trusted loop-output assumption. -/
theorem loop_execution {F : Type} (context : Context F) (steps : Nat) {before : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j)
    (remaining : j+steps = length) :
    ∃after, Exec context before loop .normal after ∧
      View after outObject outLength outStart inObject inLength inStart length owner ids old input length := by
  induction steps generalizing before j with
  | zero =>
    have he : j = length := by omega
    subst j
    exact ⟨before, .whileFalse (condition_eval context h)
      (by simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed]), h⟩
  | succ steps ih =>
    have hj : j < length := by omega
    obtain ⟨middle, first, hm⟩ := block_execution context h hj
    obtain ⟨after, rest, ha⟩ := ih hm (by omega)
    refine ⟨after, Exec.whileNext (condition_eval context h) ?_ first rest, ha⟩
    simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed, hj]

def localWrites (ids : Var → Nat) : List (String × Pointer) :=
  [("j", scalarPointer (ids Var.j) .u64)]
def arrayWrites (ids : Var → Nat) (object start : Nat) : List SourceArrayFrame.ArrayBinding :=
  [⟨"out", scalarPointer (ids Var.output) (.pointer .u64), wordPointer object start⟩]

private theorem view_bindings {F : Type} {before : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j) :
    SourceArrayFrame.Bindings before (localWrites ids) (arrayWrites ids outObject outStart) := by
  constructor
  · intro actualName pointer member
    simp only [localWrites, List.mem_singleton, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact h.locals.lookup Var.j
  · intro item member
    simp only [arrayWrites, List.mem_singleton] at member
    subst item
    exact ⟨h.locals.lookup Var.output, h.locals.read Var.output⟩
  · intro item member
    simp only [arrayWrites, List.mem_singleton] at member
    subst item
    have hd : ids Var.output ≠ ids Var.j := by intro he; have hh := h.locals.distinct he; cases hh
    have hb : ids Var.output ≠ outObject := Ne.symm (h.separate Var.output).1
    simpa [SourceArrayFrame.writes, localWrites, arrayWrites, scalarPointer, wordPointer] using And.intro hd hb

private theorem loop_writes_only (ids : Var → Nat) (object start : Nat) :
    SourceArrayFrame.Only (localWrites ids) (arrayWrites ids object start) loop := by
  simp [loop, loopBody, increment, ZeroLoop.increment, storeStmt,
    SourceArrayFrame.Only, SourceArrayFrame.Writable, localWrites, arrayWrites]

private theorem loop_no_alloc : SourceNoAlloc.Only loop := by
  simp [loop, condition, ZeroLoop.condition, loopBody, increment, ZeroLoop.increment, storeStmt,
    SourceNoAlloc.Only, SourcePure.CallFree]

/-- Every actual execution frames all caller allocations except the destination
and the local counter; this result is independent of the selected execution. -/
theorem loop_frame {F : Type} {context : Context F} {before after : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j)
    {flow : Flow} (run : Exec context before loop flow after) :
    ScanFrame.Frame before after [ids Var.j, outObject] := by
  have hf := SourceArrayFrame.exec_frame run (loop_writes_only ids outObject outStart)
    loop_no_alloc h.well (view_bindings h)
  simpa [SourceArrayFrame.writes, localWrites, arrayWrites, scalarPointer, wordPointer] using hf

/-- Source-linked copy result with actual input preservation and an unrestricted
caller-object frame. Distinct, disjoint, and identical slices are supported. -/
theorem loop_copy_output_frame {F : Type} (context : Context F) {before : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j) :
    ∃after, Exec context before loop .normal after ∧
      View after outObject outLength outStart inObject inLength inStart length owner ids old input length ∧
      (∀i, i < length → after.load (wordPointer outObject (outStart+i)) =
        some (.integer (integer64 (input i)))) ∧
      ScanFrame.Frame before after [ids Var.j, outObject] := by
  obtain ⟨after, run, ha⟩ := loop_execution context (length-j) h (by have hj := h.active; omega)
  refine ⟨after, run, ha, ?_, loop_frame h run⟩
  intro i hi
  have hib : outStart+i < outLength := by have hb := h.outBound; omega
  have hw := word_load ha.output hib
  simpa [prefixData, show outStart ≤ outStart+i ∧ outStart+i < outStart+length by omega] using hw

#print axioms contents_execution
#print axioms block_execution
#print axioms loop_execution
#print axioms loop_frame
#print axioms loop_copy_output_frame

#print axioms prefixData_step
#print axioms recursive_body_actual
#print axioms iterative_body_actual
#print axioms array_pointer_add
#print axioms store_execution
end RH080Next.FFTPV.CopyLoop
