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

inductive PVar where | out | a | b | work | i deriving DecidableEq
def pName : PVar → String | .out => "out" | .a => "a" | .b => "b" | .work => "work" | .i => "i"
def pType : PVar → CType | .i => .u64 | _ => .pointer .u64
def pValue (outObj outStart aObj aStart bObj bStart workObj workStart i : Nat) : PVar → Value
  | .out => .pointer (wordPointer outObj outStart)
  | .a => .pointer (wordPointer aObj aStart)
  | .b => .pointer (wordPointer bObj bStart)
  | .work => .pointer (wordPointer workObj workStart)
  | .i => .integer (integer64 i)
def signBit (a b : Nat) : Nat := if a=b then 0 else 1

theorem binary64_ne (a b : Nat) (ha : a<2^64) (hb : b<2^64) :
    Integer.binary .ne (integer64 a) (integer64 b)=some (.boolean (decide (a≠b))) := by
  change some (Integer.boolean (!decide ((Integer.cast .u64 (a:Int)).toInt = (Integer.cast .u64 (b:Int)).toInt))) = _
  rw [cast64_exact a ha,cast64_exact b hb,integer64_toInt,integer64_toInt]
  congr 2
  simp

/-- The real declaration and source sign branch compare the actual sixth
input words. They allocate the sign slot and preserve every older allocation. -/
theorem sign_execution {F : Type} (context : Context F) {before : State F}
    {outObj outStart aObj aSize aStart bObj bSize bStart workObj workStart i : Nat}
    {ids owners : PVar → Nat} {aData bData : Nat → Nat}
    (locals : Bindings before pName pType ids owners (pValue outObj outStart aObj aStart bObj bStart workObj workStart i))
    (well : WellScoped before) (aRep : WordArrayRep before aObj aSize aData)
    (bRep : WordArrayRep before bObj bSize bData) (aBound : aStart+6≤aSize) (bBound : bStart+6≤bSize) :
    ∃after, ExecList context before [signDeclaration,signBranch] .normal after ∧
      Bindings after (extend pName "sign") (extend pType .u64) (extend ids before.nextObject)
        (extend owners before.scope)
        (extend (pValue outObj outStart aObj aStart bObj bStart workObj workStart i)
          (.integer (integer64 (signBit (aData (aStart+5)) (bData (bStart+5)))))) ∧
      WellScoped after ∧ (∀id,id<before.nextObject → after.objects id=before.objects id) ∧
      after.nextObject=before.nextObject+1 ∧ after.scope=before.scope ∧ after.mode=before.mode := by
  have storage:=ZeroFrame.u64_storable 0 (by norm_num)
  obtain ⟨declared,decl⟩ := ZeroFrame.declare_exists well .u64 "sign" _ storage
  have d:=declare_storable storage storage.converted decl
  have wd:=wellScoped_declare well decl
  have hd:=bindings_extend_declaration locals well (by intro x;cases x <;> decide) d
  have runDecl : Exec context before signDeclaration .normal declared :=
    .declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) decl
  have freshA : aObj≠before.nextObject := by have h:=well.objectIds _ _ aRep.2.1;omega
  have freshB : bObj≠before.nextObject := by have h:=well.objectIds _ _ bRep.2.1;omega
  have ar : WordArrayRep declared aObj aSize aData := ⟨d.mode.trans aRep.1,(d.outside aObj freshA).trans aRep.2.1,aRep.2.2⟩
  have br : WordArrayRep declared bObj bSize bData := ⟨d.mode.trans bRep.1,(d.outside bObj freshB).trans bRep.2.1,bRep.2.2⟩
  have aFit:=aRep.2.2 (aStart+5) (by omega)
  have bFit:=bRep.2.2 (bStart+5) (by omega)
  have condition : Eval context declared signCondition
      (.integer (.boolean (decide (aData (aStart+5)≠bData (bStart+5))))) declared :=
    .binaryLR
      (.load (.index (.variable (hd.lookup (.inl PVar.a)) (hd.read (.inl PVar.a)))
        (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
        (slice_pointer_add ar (by omega))) (word_load ar (by omega)))
      (.load (.index (.variable (hd.lookup (.inl PVar.b)) (hd.read (.inl PVar.b)))
        (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
        (slice_pointer_add br (by omega))) (word_load br (by omega)))
      (by simp only [binary,binary64_ne _ _ aFit bFit,Option.map_some])
  by_cases same : aData (aStart+5)=bData (bStart+5)
  · refine ⟨declared,.cons runDecl (.cons (.ifFalse condition ?_) .nil),?_,wd,?_,d.nextObject,d.scope,d.mode⟩
    · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,same]
    · simpa [signBit,same] using hd
    · intro id old
      exact d.outside id (by omega)
  · obtain ⟨middle,written⟩:=scalar_store_exists (hd.enter.slots (.inr ()))
      (.integer (integer64 1)) (ZeroFrame.u64_storable _ (by norm_num))
    have assignment : Exec context declared.enterScope (.assign (v "sign") (lit 1)) .normal middle :=
      .assign (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (.variable (hd.enter.lookup (.inr ()))) written
    let after : State F := {middle.leaveScope declared.nextScope declared.environment with scope:=declared.scope}
    have blockRun : Exec context declared (.block [.assign (v "sign") (lit 1)]) .normal after :=
      .block (by rfl) (.cons assignment .nil) (by rfl)
    have only : SourceArrayFrame.Only [("sign",scalarPointer before.nextObject .u64)] []
        (.block [.assign (v "sign") (lit 1)]) := by
      simp [SourceArrayFrame.Only,SourceArrayFrame.Writable,v,lit]
    have bindings : SourceArrayFrame.Bindings declared [("sign",scalarPointer before.nextObject .u64)] [] := by
      constructor
      · intro name pointer member
        simp only [List.mem_singleton,Prod.mk.injEq] at member
        rcases member with ⟨rfl,rfl⟩
        exact hd.lookup (.inr ())
      · intro item member;cases member
      · intro item member;cases member
    have frame:=SourceArrayFrame.exec_frame blockRun only
      (by simp [SourceNoAlloc.Only,SourcePure.CallFree,v,lit]) wd bindings
    have hm:=hd.enter.store (.inr ()) (.integer (integer64 1)) (ZeroFrame.u64_storable _ (by norm_num)) written
    have eqValues : Function.update
        (extend (pValue outObj outStart aObj aStart bObj bStart workObj workStart i) (.integer (integer64 0)))
        (.inr ()) (.integer (integer64 1)) =
        extend (pValue outObj outStart aObj aStart bObj bStart workObj workStart i) (.integer (integer64 1)) := by
      funext x;cases x with
      | inl x => simp [extend,Function.update]
      | inr x => cases x;simp [extend,Function.update]
    rw [eqValues] at hm
    have leave:=hm.leave (restore:=declared.scope)
      (by intro x;exact (ne_of_lt (hd.bound x)).symm) declared.environment hd.lookup
    have wa:=(SourceNoAlloc.exec_effect blockRun (by simp [SourceNoAlloc.Only,SourcePure.CallFree,v,lit]) wd).well
    refine ⟨after,.cons runDecl (.cons (.ifTrue condition ?_ blockRun) .nil),?_,wa,?_,?_,?_,?_⟩
    · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,same]
    · simpa [signBit,same] using leave
    · intro id old
      exact (frame.outside id (by simp [SourceArrayFrame.writes,scalarPointer];omega)).trans (d.outside id (by omega))
    · exact frame.nextObject.trans d.nextObject
    · exact d.scope
    · exact frame.mode.trans d.mode

#print axioms sign_execution
end RH080Next.FFTPV.MultiplySuffix
