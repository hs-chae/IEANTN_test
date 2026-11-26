/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTProductRowLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductOuter
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame ProductInner

inductive PVar where | a | b | work | i deriving DecidableEq

def name : PVar→String | .a=>"a" | .b=>"b" | .work=>"work" | .i=>"i"
def type : PVar→CType | .a|.b|.work=>.pointer .u64 | .i=>.u64
def value (aObj aStart bObj bStart workObj workStart i : Nat) : PVar→Value
  | .a=>.pointer (wordPointer aObj aStart) | .b=>.pointer (wordPointer bObj bStart)
  | .work=>.pointer (wordPointer workObj workStart) | .i=>.integer (integer64 i)

def rowIds (ids : PVar→Nat) (j carry : Nat) : ProductInner.Var→Nat
  | .a=>ids .a | .b=>ids .b | .work=>ids .work | .i=>ids .i | .j=>j | .carry=>carry

def rowOwners (owners : PVar→Nat) (rowScope : Nat) : ProductInner.Var→Nat
  | .a=>owners .a | .b=>owners .b | .work=>owners .work | .i=>owners .i | .j|.carry=>rowScope

structure View {F : Type} (state : State F)
    (aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat)
    (ids owners : PVar→Nat) (a b data : Nat→Nat) (i : Nat) : Prop where
  work : WordArrayRep state workObj workSize data
  aInput : Slice state aObj aSize aStart a
  bInput : Slice state bObj bSize bStart b
  locals : Bindings state name type ids owners (value aObj aStart bObj bStart workObj workStart i)
  separate : ∀v,workObj≠ids v ∧ aObj≠ids v ∧ bObj≠ids v
  aShape : aObj=workObj → aSize=workSize
  bShape : bObj=workObj → bSize=workSize
  aDisjoint : aObj≠workObj ∨ aStart+5≤workStart ∨ workStart+10≤aStart
  bDisjoint : bObj≠workObj ∨ bStart+5≤workStart ∨ workStart+10≤bStart
  aBound : aStart+5≤aSize
  bBound : bStart+5≤bSize
  workBound : workStart+10≤workSize
  aDigits : ∀k,k<5 → a k<1000000000
  bDigits : ∀k,k<5 → b k<1000000000
  workDigits : ∀k,k<10 → data (workStart+k)<1000000000
  row : i≤5
  well : WellScoped state

def rowDeclarations : List Stmt:=[.declare .u64 "j" (some (.literal (.integer 0 "ULL"))),
  .declare .u64 "carry" (some (.literal (.integer 0 "ULL")))]

/-- The application's own row initialization really allocates and initializes
j and carry in the current block scope; all four persistent bindings keep
their earlier owners. There is no initial-application-state assumption. -/
theorem initialize_row {F : Type} (context : Context F) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart i : Nat}
    {ids owners : PVar→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data i)
    (hi : i<5) :
    ∃after,ExecList context before rowDeclarations .normal after ∧
      ProductInner.View after aObj aSize aStart bObj bSize bStart workObj workSize workStart
        (rowIds ids before.nextObject (before.nextObject+1)) (rowOwners owners before.scope) a b data i 0 0 ∧
      Frame before.nextObject before after [] := by
  obtain ⟨jState,jDeclared⟩:=ZeroFrame.declare_exists h.well .u64 "j" (.integer (integer64 0))
    (ZeroFrame.u64_storable 0 (by norm_num))
  have dj : Declaration before jState "j" .u64 (.integer (integer64 0)):=
    declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) jDeclared
  have jw:=wellScoped_declare h.well jDeclared
  have jl:=h.locals.declare h.well (by intro v;cases v <;> decide) dj
  obtain ⟨cState,cDeclared⟩:=ZeroFrame.declare_exists jw .u64 "carry" (.integer (integer64 0))
    (ZeroFrame.u64_storable 0 (by norm_num))
  have dc : Declaration jState cState "carry" .u64 (.integer (integer64 0)):=
    declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) cDeclared
  have cw:=wellScoped_declare jw cDeclared
  have cl:=jl.declare jw (by intro v;cases v <;> decide) dc
  have wc:=array_declare_old jw (array_declare_old h.well h.work dj) dc
  have ac:=ProductInner.slice_declare jw (ProductInner.slice_declare h.well h.aInput dj) dc
  have bc:=ProductInner.slice_declare jw (ProductInner.slice_declare h.well h.bInput dj) dc
  have oldBound : ∀v,ids v<before.nextObject:=fun v=>h.well.objectIds _ _ (h.locals.slots v).object
  have workOld:=h.well.objectIds _ _ h.work.2.1
  obtain ⟨ad,aRep,aVals⟩:=h.aInput
  obtain ⟨bd,bRep,bVals⟩:=h.bInput
  have aOld:=h.well.objectIds _ _ aRep.2.1
  have bOld:=h.well.objectIds _ _ bRep.2.1
  have jSlot:=slot_declare_old jw dj.slot dc
  have cSlot : Slot cState (before.nextObject+1) before.scope .u64 (.integer (integer64 0)):=by
    rw [←dj.nextObject,←dj.scope]
    exact dc.slot
  have jNamed : cState.environment.lookup "j"=some (scalarPointer before.nextObject .u64):=by
    rw [dc.environment,dj.environment];rfl
  have cNamed : cState.environment.lookup "carry"=some (scalarPointer (before.nextObject+1) .u64):=by
    rw [dc.environment,dj.nextObject];rfl
  have allLocals : Bindings cState ProductInner.name ProductInner.type
      (rowIds ids before.nextObject (before.nextObject+1)) (rowOwners owners before.scope)
      (ProductInner.value aObj aStart bObj bStart workObj workStart i 0 0):=by
    refine ⟨?_,?_,?_,?_⟩
    · intro v;cases v
      · exact cl.lookup PVar.a
      · exact cl.lookup PVar.b
      · exact cl.lookup PVar.work
      · exact cl.lookup PVar.i
      · exact jNamed
      · exact cNamed
    · intro v;cases v
      · exact cl.slots PVar.a
      · exact cl.slots PVar.b
      · exact cl.slots PVar.work
      · exact cl.slots PVar.i
      · exact jSlot
      · exact cSlot
    · intro u v equal
      cases u <;> cases v
      · rfl
      · change ids PVar.a=ids PVar.b at equal
        exact False.elim ((by decide : PVar.a≠PVar.b) (h.locals.distinct equal))
      · change ids PVar.a=ids PVar.work at equal
        exact False.elim ((by decide : PVar.a≠PVar.work) (h.locals.distinct equal))
      · change ids PVar.a=ids PVar.i at equal
        exact False.elim ((by decide : PVar.a≠PVar.i) (h.locals.distinct equal))
      · change ids PVar.a=before.nextObject at equal
        have old:=oldBound PVar.a
        omega
      · change ids PVar.a=before.nextObject+1 at equal
        have old:=oldBound PVar.a
        omega
      · change ids PVar.b=ids PVar.a at equal
        exact False.elim ((by decide : PVar.b≠PVar.a) (h.locals.distinct equal))
      · rfl
      · change ids PVar.b=ids PVar.work at equal
        exact False.elim ((by decide : PVar.b≠PVar.work) (h.locals.distinct equal))
      · change ids PVar.b=ids PVar.i at equal
        exact False.elim ((by decide : PVar.b≠PVar.i) (h.locals.distinct equal))
      · change ids PVar.b=before.nextObject at equal
        have old:=oldBound PVar.b
        omega
      · change ids PVar.b=before.nextObject+1 at equal
        have old:=oldBound PVar.b
        omega
      · change ids PVar.work=ids PVar.a at equal
        exact False.elim ((by decide : PVar.work≠PVar.a) (h.locals.distinct equal))
      · change ids PVar.work=ids PVar.b at equal
        exact False.elim ((by decide : PVar.work≠PVar.b) (h.locals.distinct equal))
      · rfl
      · change ids PVar.work=ids PVar.i at equal
        exact False.elim ((by decide : PVar.work≠PVar.i) (h.locals.distinct equal))
      · change ids PVar.work=before.nextObject at equal
        have old:=oldBound PVar.work
        omega
      · change ids PVar.work=before.nextObject+1 at equal
        have old:=oldBound PVar.work
        omega
      · change ids PVar.i=ids PVar.a at equal
        exact False.elim ((by decide : PVar.i≠PVar.a) (h.locals.distinct equal))
      · change ids PVar.i=ids PVar.b at equal
        exact False.elim ((by decide : PVar.i≠PVar.b) (h.locals.distinct equal))
      · change ids PVar.i=ids PVar.work at equal
        exact False.elim ((by decide : PVar.i≠PVar.work) (h.locals.distinct equal))
      · rfl
      · change ids PVar.i=before.nextObject at equal
        have old:=oldBound PVar.i
        omega
      · change ids PVar.i=before.nextObject+1 at equal
        have old:=oldBound PVar.i
        omega
      · change before.nextObject=ids PVar.a at equal
        have old:=oldBound PVar.a
        omega
      · change before.nextObject=ids PVar.b at equal
        have old:=oldBound PVar.b
        omega
      · change before.nextObject=ids PVar.work at equal
        have old:=oldBound PVar.work
        omega
      · change before.nextObject=ids PVar.i at equal
        have old:=oldBound PVar.i
        omega
      · rfl
      · change before.nextObject=before.nextObject+1 at equal
        omega
      · change before.nextObject+1=ids PVar.a at equal
        have old:=oldBound PVar.a
        omega
      · change before.nextObject+1=ids PVar.b at equal
        have old:=oldBound PVar.b
        omega
      · change before.nextObject+1=ids PVar.work at equal
        have old:=oldBound PVar.work
        omega
      · change before.nextObject+1=ids PVar.i at equal
        have old:=oldBound PVar.i
        omega
      · change before.nextObject+1=before.nextObject at equal
        omega
      · rfl
    · intro v;cases v
      · exact cl.bound PVar.a
      · exact cl.bound PVar.b
      · exact cl.bound PVar.work
      · exact cl.bound PVar.i
      · change before.scope<cState.nextScope
        rw [dc.nextScope,dj.nextScope];exact h.well.current
      · change before.scope<cState.nextScope
        rw [dc.nextScope,dj.nextScope];exact h.well.current
  have separate : ∀v,workObj≠rowIds ids before.nextObject (before.nextObject+1) v ∧
      aObj≠rowIds ids before.nextObject (before.nextObject+1) v ∧
      bObj≠rowIds ids before.nextObject (before.nextObject+1) v := by
    intro v;cases v
    · exact h.separate PVar.a
    · exact h.separate PVar.b
    · exact h.separate PVar.work
    · exact h.separate PVar.i
    · simp only [rowIds];omega
    · simp only [rowIds];omega
  have first : Frame before.nextObject before jState []:=
    ApplicationBirthFrame.declare_frame _ _ h.well (le_refl _) jDeclared
  have second : Frame before.nextObject jState cState []:=
    ApplicationBirthFrame.declare_frame _ _ jw (by rw [dj.nextObject];omega) cDeclared
  exact ⟨cState,.cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) jDeclared)
    (.cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) cDeclared) .nil),
    ⟨wc,ac,bc,allLocals,separate,h.aShape,h.bShape,h.aDisjoint,h.bDisjoint,h.aBound,h.bBound,h.workBound,
      h.aDigits,h.bDigits,h.workDigits,by norm_num,hi,by norm_num,cw⟩,first.trans second⟩

#print axioms initialize_row
end RH080Next.FFTPV.ProductOuter
