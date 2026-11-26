/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixBindings
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner

inductive MVar where | out | work | i | sign | lost deriving DecidableEq
def midName : MVar → String
  | .out => "out" | .work => "work" | .i => "i" | .sign => "sign" | .lost => "lost"
def midType : MVar → CType | .out | .work => .pointer .u64 | _ => .u64
def midValues (outObj outStart workObj workStart i sign lost : Nat) : MVar → Value
  | .out => .pointer (wordPointer outObj outStart)
  | .work => .pointer (wordPointer workObj workStart)
  | .i => .integer (integer64 i)
  | .sign => .integer (integer64 sign)
  | .lost => .integer (integer64 lost)
def lostMap : LVar → MVar | .work => .work | .lost => .lost | .i => .i
def copyMap : CVar → MVar | .out => .out | .work => .work | .i => .i
private theorem lostMap_injective : Function.Injective lostMap := by intro a b eq;cases a <;> cases b <;> cases eq <;> rfl
private theorem copyMap_injective : Function.Injective copyMap := by intro a b eq;cases a <;> cases b <;> cases eq <;> rfl
private theorem lost_name : midName ∘ lostMap = lostName := by funext x;cases x <;> rfl
private theorem lost_type : midType ∘ lostMap = lostType := by funext x;cases x <;> rfl
private theorem copy_name : midName ∘ copyMap = copyName := by funext x;cases x <;> rfl
private theorem copy_type : midType ∘ copyMap = copyType := by funext x;cases x <;> rfl

theorem lost_bindings {F : Type} {state : State F}
    {outObj outStart workObj workStart j sign : Nat} {data : Nat → Nat} {ids owners : MVar → Nat}
    (h : Bindings state midName midType ids owners
      (midValues outObj outStart workObj workStart j sign (CanonicalSource.digitSum data workStart j))) :
    Bindings state lostName lostType (ids ∘ lostMap) (owners ∘ lostMap) (lostValues workObj workStart data j) := by
  have hb:=bindings_reindex h lostMap lostMap_injective
  rw [lost_name,lost_type] at hb
  have values : midValues outObj outStart workObj workStart j sign
      (CanonicalSource.digitSum data workStart j) ∘ lostMap = lostValues workObj workStart data j := by
    funext x;cases x <;> rfl
  rwa [values] at hb

theorem copy_bindings {F : Type} {state : State F}
    {outObj outStart workObj workStart j sign lost : Nat} {ids owners : MVar → Nat}
    (h : Bindings state midName midType ids owners (midValues outObj outStart workObj workStart j sign lost)) :
    Bindings state copyName copyType (ids ∘ copyMap) (owners ∘ copyMap) (copyValues outObj outStart workObj workStart j) := by
  have hb:=bindings_reindex h copyMap copyMap_injective
  rw [copy_name,copy_type] at hb
  have values : midValues outObj outStart workObj workStart j sign lost ∘ copyMap =
      copyValues outObj outStart workObj workStart j := by funext x;cases x <;> rfl
  rwa [values] at hb

/-- Complete real environment for the existing low-word sum/copy source loops. -/
structure MiddleView {F : Type} (state : State F)
    (outObj outSize outStart workObj workSize workStart : Nat)
    (ids owners : MVar → Nat) (old data : Nat → Nat) (i sign lost : Nat) : Prop where
  outRep : WordArrayRep state outObj outSize old
  workRep : WordArrayRep state workObj workSize data
  locals : Bindings state midName midType ids owners (midValues outObj outStart workObj workStart i sign lost)
  separate : ∀v,outObj≠ids v ∧ workObj≠ids v
  shape : workObj=outObj → workSize=outSize
  disjoint : outObj≠workObj ∨ outStart+6≤workStart ∨ workStart+10≤outStart
  outBound : outStart+6≤outSize
  workBound : workStart+10≤workSize
  digits : ∀k,k<10 → data (workStart+k)<1000000000
  well : WellScoped state

/-- The actual reset assignment updates the persistent i slot, leaving every
array and every other scalar binding unchanged. -/
theorem reset_execution {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart i sign lost : Nat}
    {ids owners : MVar → Nat} {old data : Nat → Nat}
    (h : MiddleView before outObj outSize outStart workObj workSize workStart ids owners old data i sign lost) :
    ∃after,Exec context before resetIndex .normal after ∧
      MiddleView after outObj outSize outStart workObj workSize workStart ids owners old data 0 sign lost := by
  obtain ⟨after,written⟩:=scalar_store_exists (h.locals.slots MVar.i)
    (.integer (integer64 0)) (ZeroFrame.u64_storable _ (by norm_num))
  have run : Exec context before resetIndex .normal after :=
    .assign (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) (.variable (h.locals.lookup MVar.i)) written
  have locals:=h.locals.store MVar.i (.integer (integer64 0)) (ZeroFrame.u64_storable _ (by norm_num)) written
  have values : Function.update (midValues outObj outStart workObj workStart i sign lost) MVar.i
      (.integer (integer64 0)) = midValues outObj outStart workObj workStart 0 sign lost := by
    funext x;cases x <;> simp [midValues,Function.update]
  rw [values] at locals
  obtain ⟨env,mode,scope,ns,no,outside⟩:=SourceLocals.store_frame written
  exact ⟨after,run,
    ⟨mode.trans h.outRep.1,(outside outObj (h.separate MVar.i).1).trans h.outRep.2.1,h.outRep.2.2⟩,
    ⟨mode.trans h.workRep.1,(outside workObj (h.separate MVar.i).2).trans h.workRep.2.1,h.workRep.2.2⟩,
    locals,h.separate,h.shape,h.disjoint,h.outBound,h.workBound,h.digits,wellScoped_store h.well written⟩

/-- The four actual low-product words are accumulated by the source, while
out/work/sign and all unrelated caller allocations remain unchanged. -/
theorem middle_lost_execution {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign : Nat}
    {ids owners : MVar → Nat} {old data : Nat → Nat}
    (h : MiddleView before outObj outSize outStart workObj workSize workStart ids owners old data 0 sign 0) :
    ∃after,Exec context before lostLoop .normal after ∧
      MiddleView after outObj outSize outStart workObj workSize workStart ids owners old data 4 sign
        (CanonicalSource.digitSum data workStart 4) := by
  have lv : LostView before workObj workSize workStart (ids ∘ lostMap) (owners ∘ lostMap) data 0 := by
    refine ⟨h.workRep,?_,fun v => (h.separate (lostMap v)).2,h.workBound,h.digits,h.well,by omega⟩
    apply lost_bindings
    simpa [CanonicalSource.digitSum_zero] using h.locals
  obtain ⟨after,run,ha⟩:=lost_loop_execution context 4 lv (by omega)
  have frame:=lost_loop_frame lv run
  have localAfter : Bindings after midName midType ids owners
      (midValues outObj outStart workObj workStart 4 sign (CanonicalSource.digitSum data workStart 4)) := by
    refine ⟨?_,?_,h.locals.distinct,fun v => (h.locals.bound v).trans_le frame.nextScope⟩
    · intro v;rw [frame.environment];exact h.locals.lookup v
    · intro v
      cases v with
      | i => exact ha.locals.slots LVar.i
      | lost => exact ha.locals.slots LVar.lost
      | out =>
        apply slot_scan_frame (h.locals.slots MVar.out) frame
        simp [Function.comp_def,lostMap]
        constructor <;> intro eq <;> have bad:=h.locals.distinct eq <;> cases bad
      | work =>
        apply slot_scan_frame (h.locals.slots MVar.work) frame
        simp [Function.comp_def,lostMap]
        constructor <;> intro eq <;> have bad:=h.locals.distinct eq <;> cases bad
      | sign =>
        apply slot_scan_frame (h.locals.slots MVar.sign) frame
        simp [Function.comp_def,lostMap]
        constructor <;> intro eq <;> have bad:=h.locals.distinct eq <;> cases bad
  have outRep : WordArrayRep after outObj outSize old :=
    ⟨frame.mode.trans h.outRep.1,(frame.outside outObj (by simp [Function.comp_def,lostMap,(h.separate MVar.lost).1,
      (h.separate MVar.i).1])).trans h.outRep.2.1,h.outRep.2.2⟩
  exact ⟨after,run,outRep,ha.work,localAfter,h.separate,h.shape,h.disjoint,h.outBound,h.workBound,h.digits,ha.well⟩

/-- Actual retained-digit copy, including the environment needed by the
following sign, overflow, rounding and canonicalization instructions. Workspace
preservation is stated per protected word, allowing shared allocations. -/
theorem middle_copy_execution {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost : Nat}
    {ids owners : MVar → Nat} {old data : Nat → Nat}
    (h : MiddleView before outObj outSize outStart workObj workSize workStart ids owners old data 0 sign lost) :
    ∃after,Exec context before copyLoop .normal after ∧
      CopyView after outObj outSize outStart workObj workSize workStart (ids ∘ copyMap) (owners ∘ copyMap)
        old (fun k => data (workStart+k)) 5 ∧
      Bindings after midName midType ids owners (midValues outObj outStart workObj workStart 5 sign lost) := by
  have cv : CopyView before outObj outSize outStart workObj workSize workStart (ids ∘ copyMap) (owners ∘ copyMap)
      old (fun k => data (workStart+k)) 0 := by
    refine ⟨?_,⟨data,h.workRep,fun _ _ => rfl⟩,copy_bindings h.locals,
      fun v => h.separate (copyMap v),h.shape,h.disjoint,h.outBound,h.workBound,h.well,by omega⟩
    simpa only [copied,CopyLoop.prefixData_zero] using h.outRep
  obtain ⟨after,run,ha⟩:=copy_loop_execution context 5 cv (by omega)
  have frame:=copy_loop_frame cv run
  have localAfter : Bindings after midName midType ids owners (midValues outObj outStart workObj workStart 5 sign lost) := by
    refine ⟨?_,?_,h.locals.distinct,fun v => (h.locals.bound v).trans_le frame.nextScope⟩
    · intro v;rw [frame.environment];exact h.locals.lookup v
    · intro v
      cases v with
      | i => exact ha.locals.slots CVar.i
      | out =>
        apply slot_scan_frame (h.locals.slots MVar.out) frame
        simp [copyMap,(h.separate MVar.out).1.symm]
        intro eq;have bad:=h.locals.distinct eq;cases bad
      | work =>
        apply slot_scan_frame (h.locals.slots MVar.work) frame
        simp [copyMap,(h.separate MVar.work).1.symm]
        intro eq;have bad:=h.locals.distinct eq;cases bad
      | sign =>
        apply slot_scan_frame (h.locals.slots MVar.sign) frame
        simp [copyMap,(h.separate MVar.sign).1.symm]
        intro eq;have bad:=h.locals.distinct eq;cases bad
      | lost =>
        apply slot_scan_frame (h.locals.slots MVar.lost) frame
        simp [copyMap,(h.separate MVar.lost).1.symm]
        intro eq;have bad:=h.locals.distinct eq;cases bad
  exact ⟨after,run,ha,localAfter⟩

/-- The complete actual loss/reset/copy sequence, with exact low-word sum
and exact retained digits. No numerical answer is assumed. -/
theorem middle_execution {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign : Nat}
    {ids owners : MVar → Nat} {old data : Nat → Nat}
    (h : MiddleView before outObj outSize outStart workObj workSize workStart ids owners old data 0 sign 0) :
    ∃after,ExecList context before [lostLoop,resetIndex,copyLoop] .normal after ∧
      CopyView after outObj outSize outStart workObj workSize workStart (ids ∘ copyMap) (owners ∘ copyMap)
        old (fun k => data (workStart+k)) 5 ∧
      Bindings after midName midType ids owners
        (midValues outObj outStart workObj workStart 5 sign (CanonicalSource.digitSum data workStart 4)) := by
  obtain ⟨s1,r1,h1⟩:=middle_lost_execution context h
  obtain ⟨s2,r2,h2⟩:=reset_execution context h1
  obtain ⟨after,r3,h3,locals⟩:=middle_copy_execution context h2
  exact ⟨after,.cons r1 (.cons r2 (.cons r3 .nil)),h3,locals⟩

#print axioms middle_copy_execution
#print axioms middle_execution

#print axioms reset_execution
#print axioms middle_lost_execution
end RH080Next.FFTPV.MultiplySuffix
