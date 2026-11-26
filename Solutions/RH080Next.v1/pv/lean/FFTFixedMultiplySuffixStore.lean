/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixMiddle
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner

/-- A real store to any of the six output words preserves all ten scratch
words, including when output and scratch share a disjoint allocation. -/
theorem protected_output_store {F : Type} {before : State F}
    {outObj outSize outStart workObj workSize workStart index value : Nat}
    {old data scratch : Nat → Nat}
    (outRep : WordArrayRep before outObj outSize old) (workRep : WordArrayRep before workObj workSize data)
    (workValues : ∀k,k<10 → data (workStart+k)=scratch k)
    (shape : workObj=outObj → workSize=outSize)
    (disjoint : outObj≠workObj ∨ outStart+6≤workStart ∨ workStart+10≤outStart)
    (outBound : outStart+6≤outSize) (workBound : workStart+10≤workSize)
    (hi : index<6) (fit : value<2^64) :
    ∃after,before.store (wordPointer outObj (outStart+index)) (.integer (integer64 value))=some after ∧
      WordArrayRep after outObj outSize (Function.update old (outStart+index) value) ∧
      (∃data',WordArrayRep after workObj workSize data' ∧ ∀k,k<10 → data' (workStart+k)=scratch k) := by
  obtain ⟨after,written,outAfter⟩:=word_store_with_rep (index := outStart+index) outRep (by omega) fit
  refine ⟨after,written,outAfter,?_⟩
  by_cases same : workObj=outObj
  · have sz:=shape same
    subst workObj;subst workSize
    refine ⟨Function.update old (outStart+index) value,outAfter,?_⟩
    intro k hk
    have bound : workStart+k<outSize := by omega
    have different : workStart+k≠outStart+index := by
      rcases disjoint with no | lo | hi
      · exact False.elim (no rfl)
      · omega
      · omega
    rw [Function.update_of_ne different]
    exact (word_data_unique outRep workRep _ bound).trans (workValues k hk)
  · obtain ⟨env,mode,scope,ns,no,outside⟩:=SourceLocals.store_frame written
    exact ⟨data,⟨mode.trans workRep.1,(outside workObj same).trans workRep.2.1,workRep.2.2⟩,workValues⟩

/-- Concrete post-copy arrays and the actual source scalar environment. -/
structure TailView {F : Type} (state : State F)
    (outObj outSize outStart workObj workSize workStart : Nat)
    (ids owners : MVar → Nat) (outData scratch : Nat → Nat) (sign lost : Nat) : Prop where
  output : WordArrayRep state outObj outSize outData
  work : ∃data,WordArrayRep state workObj workSize data ∧ ∀k,k<10 → data (workStart+k)=scratch k
  locals : Bindings state midName midType ids owners (midValues outObj outStart workObj workStart 5 sign lost)
  separate : ∀v,outObj≠ids v ∧ workObj≠ids v
  shape : workObj=outObj → workSize=outSize
  disjoint : outObj≠workObj ∨ outStart+6≤workStart ∨ workStart+10≤outStart
  outBound : outStart+6≤outSize
  workBound : workStart+10≤workSize
  digits : ∀k,k<10 → scratch k<1000000000
  signBound : sign≤1
  well : WellScoped state

/-- Actual out[5]=sign executes after copying retained digits. -/
theorem sign_store_execution {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost : Nat}
    {ids owners : MVar → Nat} {old scratch : Nat → Nat}
    (h : CopyView before outObj outSize outStart workObj workSize workStart (ids ∘ copyMap) (owners ∘ copyMap) old scratch 5)
    (locals : Bindings before midName midType ids owners (midValues outObj outStart workObj workStart 5 sign lost))
    (separate : ∀v,outObj≠ids v ∧ workObj≠ids v) (digits : ∀k,k<10 → scratch k<1000000000) (signBound : sign≤1) :
    ∃after,Exec context before signStore .normal after ∧
      TailView after outObj outSize outStart workObj workSize workStart ids owners
        (Function.update (copied old scratch outStart 5) (outStart+5) sign) scratch sign lost := by
  obtain ⟨data,workRep,workValues⟩:=h.work
  obtain ⟨after,written,outAfter,workAfter⟩:=protected_output_store h.output workRep workValues
    h.shape h.disjoint h.outBound h.workBound (by omega : 5<6) (by omega : sign<2^64)
  have run : Exec context before signStore .normal after :=
    .assign (.variable (locals.lookup MVar.sign) (locals.read MVar.sign))
      (.index (.variable (locals.lookup MVar.out) (locals.read MVar.out))
        (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
        (slice_pointer_add h.output (by have hb:=h.outBound;omega))) written
  exact ⟨after,run,outAfter,workAfter,locals.store_other (fun x => (separate x).1.symm) written,
    separate,h.shape,h.disjoint,h.outBound,h.workBound,digits,signBound,wellScoped_store h.well written⟩

/-- The real overflow declaration reads the tenth protected product word,
allocates a genuine typed local, and preserves both application slices. -/
theorem overflow_declaration_execution {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost : Nat}
    {ids owners : MVar → Nat} {outData scratch : Nat → Nat}
    (h : TailView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost) :
    ∃after,Exec context before overflowDeclaration .normal after ∧
      TailView after outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost ∧
      Bindings after (extend midName "overflow") (extend midType .u64) (extend ids before.nextObject)
        (extend owners before.scope)
        (extend (midValues outObj outStart workObj workStart 5 sign lost) (.integer (integer64 (scratch 9)))) := by
  have storage:=ZeroFrame.u64_storable (scratch 9) (by have bound:=h.digits 9 (by omega);omega)
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists h.well .u64 "overflow" _ storage
  have d:=declare_storable storage storage.converted declared
  obtain ⟨data,workRep,workValues⟩:=h.work
  have inputRead : before.load (wordPointer workObj (workStart+9))=some (.integer (integer64 (scratch 9))) := by
    rw [←workValues 9 (by omega)]
    exact word_load workRep (by have hb:=h.workBound;omega)
  have run : Exec context before overflowDeclaration .normal after :=
    .declareSome (.load (.index (.variable (h.locals.lookup MVar.work) (h.locals.read MVar.work))
      (.literal (.integer 9 "ULL") _ (.integer (integer64 9)) (by rfl))
      (slice_pointer_add workRep (by have hb:=h.workBound;omega))) inputRead) declared
  have locals:=bindings_extend_declaration h.locals h.well (by intro x;cases x <;> decide) d
  have outOld:=h.well.objectIds _ _ h.output.2.1
  have workOld:=h.well.objectIds _ _ workRep.2.1
  have outAfter : WordArrayRep after outObj outSize outData :=
    ⟨d.mode.trans h.output.1,(d.outside outObj (by omega)).trans h.output.2.1,h.output.2.2⟩
  have workAfter : WordArrayRep after workObj workSize data :=
    ⟨d.mode.trans workRep.1,(d.outside workObj (by omega)).trans workRep.2.1,workRep.2.2⟩
  exact ⟨after,run,
    ⟨outAfter,⟨data,workAfter,workValues⟩,h.locals.declare h.well (by intro x;cases x <;> decide) d,
      h.separate,h.shape,h.disjoint,h.outBound,h.workBound,h.digits,h.signBound,wellScoped_declare h.well declared⟩,
    locals⟩

#print axioms protected_output_store
#print axioms sign_store_execution
#print axioms overflow_declaration_execution
end RH080Next.FFTPV.MultiplySuffix
