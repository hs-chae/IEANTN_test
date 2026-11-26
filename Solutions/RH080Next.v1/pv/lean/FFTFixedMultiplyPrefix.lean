/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyParameters
import FFTZeroSliceCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyParameters
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

def coreIds (parameterIds : Var→Nat) (iId : Nat) : ProductOuter.PVar→Nat
  | .a=>parameterIds .a | .b=>parameterIds .b | .work=>parameterIds .work | .i=>iId

def zeroCall : Stmt:=.expression (.call "zero_words" [.variable "work",.literal (.integer 10 "ULL")])
def iDeclaration : Stmt:=.declare .u64 "i" (some (.literal (.integer 0 "ULL")))

theorem actual_prefix : (ProductRow.items fixed_multiply_ast.body).take 2=[zeroCall,iDeclaration]:=by rfl

/-- This proves the unchanged six input words from the actual zero_words
helper output. Same-allocation input/scratch slices are handled explicitly. -/
theorem zeroized_input {F : Type} {before after : State F}
    {workObj workSize workStart object size start : Nat} {workData input : Nat→Nat}
    (well : WellScoped before) (work : WordArrayRep before workObj workSize workData)
    (rep : WordArrayRep before object size input)
    (shape : object=workObj → size=workSize)
    (disjoint : object≠workObj ∨ start+6≤workStart ∨ workStart+10≤start)
    (bound : start+6≤size)
    (zeroed : WordArrayRep after workObj workSize (ZeroSlice.zeroData workData workStart 10))
    (frame : CopyLoop.CallerFrame before after workObj) :
    ∃data,WordArrayRep after object size data ∧ ∀k,k<6 → data (start+k)=input (start+k) := by
  by_cases same : object=workObj
  · have sizes:=shape same
    subst object;subst size
    refine ⟨ZeroSlice.zeroData workData workStart 10,zeroed,?_⟩
    intro k hk
    rw [ZeroSlice.zeroData_outside _ _ _ _ (by rcases disjoint with no | low | high <;> omega)]
    exact word_data_unique work rep _ (by omega)
  · have old:=well.objectIds _ _ rep.2.1
    exact ⟨input,⟨zeroed.1,(frame.objects object old same).trans rep.2.1,rep.2.2⟩,fun _ _=>rfl⟩

/-- Actual source prefix after the real parameter binding: zero_words is
called through the program's actual function lookup, and i is genuinely born.
It supplies the core's zero scratch and mixed-scope entry invariant. -/
theorem prefix_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast) {before : State F}
    {outObj outStart aObj aSize aStart bObj bSize bStart workObj workSize workStart owner : Nat}
    {parameterIds : Var→Nat} {aData bData workData : Nat→Nat}
    (well : WellScoped before)
    (params : Locals before name type parameterIds owner (value outObj outStart aObj aStart bObj bStart workObj workStart))
    (ownerCurrent : owner=before.scope)
    (latestParameter : before.nextObject=parameterIds Var.work+1)
    (freshScope : before.nextScope=owner+1)
    (work : WordArrayRep before workObj workSize workData)
    (aRep : WordArrayRep before aObj aSize aData) (bRep : WordArrayRep before bObj bSize bData)
    (aShape : aObj=workObj → aSize=workSize) (bShape : bObj=workObj → bSize=workSize)
    (aDisjoint : aObj≠workObj ∨ aStart+6≤workStart ∨ workStart+10≤aStart)
    (bDisjoint : bObj≠workObj ∨ bStart+6≤workStart ∨ workStart+10≤bStart)
    (aBound : aStart+6≤aSize) (bBound : bStart+6≤bSize) (workBound : workStart+10≤workSize)
    (aDigits : ∀k,k<5 → aData (aStart+k)<1000000000)
    (bDigits : ∀k,k<5 → bData (bStart+k)<1000000000)
    (separate : ∀v,workObj≠parameterIds v ∧ aObj≠parameterIds v ∧ bObj≠parameterIds v) :
    ∃after iId,ExecList context before [zeroCall,iDeclaration] .normal after ∧
      ProductOuter.View after aObj aSize aStart bObj bSize bStart workObj workSize workStart
        (coreIds parameterIds iId) (fun _=>owner)
        (fun k=>aData (aStart+k)) (fun k=>bData (bStart+k)) (ZeroSlice.zeroData workData workStart 10) 0 ∧
      Locals after name type parameterIds owner (value outObj outStart aObj aStart bObj bStart workObj workStart) ∧
      (∀v,parameterIds v < iId) ∧ Frame before.nextObject before after [workObj] ∧
      (∀k,k<6 → after.load (wordPointer aObj (aStart+k))=some (.integer (integer64 (aData (aStart+k))))) ∧
      (∀k,k<6 → after.load (wordPointer bObj (bStart+k))=some (.integer (integer64 (bData (bStart+k))))) := by
  obtain ⟨zeroState,zeroRun,zeroed,zeroFrame⟩:=ZeroSlice.zero_words_call context selected before
    workObj workSize workStart 10 workData well work workBound (by norm_num)
  have arguments : Args context before [.variable "work",.literal (.integer 10 "ULL")]
      [.pointer (wordPointer workObj workStart),.integer (integer64 10)] before:=by
    refine .ordered (List.Perm.refl _) (.cons (.variable (params.lookup Var.work) (params.read Var.work))
      (.cons (.literal (.integer 10 "ULL") _ (.integer (integer64 10)) (by rfl)) .nil)) ?_
    exact .cons rfl (.cons rfl .nil)
  have zeroExec : Exec context before zeroCall .normal zeroState:=.expression (.call arguments zeroRun)
  have zslots : ∀v,Slot zeroState (parameterIds v) owner (type v)
      (value outObj outStart aObj aStart bObj bStart workObj workStart v):=by
    intro v
    have old:=well.objectIds _ _ (params.slots v).object
    exact ⟨(params.slots v).storable,by rw [zeroFrame.objects _ old (separate v).1.symm];exact (params.slots v).object⟩
  have zl : Locals zeroState name type parameterIds owner
      (value outObj outStart aObj aStart bObj bStart workObj workStart):=by
    refine ⟨?_,zslots,params.distinct,?_⟩
    · rw [zeroFrame.environment];exact params.lookup
    · exact zeroFrame.well.automatic _ _ owner (zslots Var.work).object (by rfl)
  obtain ⟨ad,ar,av⟩:=zeroized_input well work aRep aShape aDisjoint aBound zeroed zeroFrame
  obtain ⟨bd,br,bv⟩:=zeroized_input well work bRep bShape bDisjoint bBound zeroed zeroFrame
  obtain ⟨after,iDeclared⟩:=ZeroFrame.declare_exists zeroFrame.well .u64 "i" (.integer (integer64 0))
    (ZeroFrame.u64_storable 0 (by norm_num))
  have di : Declaration zeroState after "i" .u64 (.integer (integer64 0)):=
    declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) iDeclared
  have afterW:=wellScoped_declare zeroFrame.well iDeclared
  have il:=locals_declare_old zeroFrame.well zl (by intro v;cases v <;> decide) di
  have wa:=array_declare_old zeroFrame.well zeroed di
  have aa:=array_declare_old zeroFrame.well ar di
  have ba:=array_declare_old zeroFrame.well br di
  have iSlot : Slot after zeroState.nextObject owner .u64 (.integer (integer64 0)):=by
    rw [ownerCurrent,←zeroFrame.scope];exact di.slot
  have iNamed : after.environment.lookup "i"=some (scalarPointer zeroState.nextObject .u64):=by
    rw [di.environment];rfl
  have oldIds : ∀v,parameterIds v<zeroState.nextObject:=fun v=>zeroFrame.well.objectIds _ _ (zslots v).object
  have locals : ProductInner.Bindings after ProductOuter.name ProductOuter.type
      (coreIds parameterIds zeroState.nextObject) (fun _=>owner)
      (ProductOuter.value aObj aStart bObj bStart workObj workStart 0):=by
    refine ⟨?_,?_,?_,?_⟩
    · intro v;cases v
      · exact il.lookup Var.a
      · exact il.lookup Var.b
      · exact il.lookup Var.work
      · exact iNamed
    · intro v;cases v
      · exact il.slots Var.a
      · exact il.slots Var.b
      · exact il.slots Var.work
      · exact iSlot
    · intro u v equal
      cases u <;> cases v
      · rfl
      · change parameterIds Var.a=parameterIds Var.b at equal
        exact False.elim ((by decide : Var.a≠Var.b) (params.distinct equal))
      · change parameterIds Var.a=parameterIds Var.work at equal
        exact False.elim ((by decide : Var.a≠Var.work) (params.distinct equal))
      · change parameterIds Var.a=zeroState.nextObject at equal
        have old:=oldIds Var.a
        omega
      · change parameterIds Var.b=parameterIds Var.a at equal
        exact False.elim ((by decide : Var.b≠Var.a) (params.distinct equal))
      · rfl
      · change parameterIds Var.b=parameterIds Var.work at equal
        exact False.elim ((by decide : Var.b≠Var.work) (params.distinct equal))
      · change parameterIds Var.b=zeroState.nextObject at equal
        have old:=oldIds Var.b
        omega
      · change parameterIds Var.work=parameterIds Var.a at equal
        exact False.elim ((by decide : Var.work≠Var.a) (params.distinct equal))
      · change parameterIds Var.work=parameterIds Var.b at equal
        exact False.elim ((by decide : Var.work≠Var.b) (params.distinct equal))
      · rfl
      · change parameterIds Var.work=zeroState.nextObject at equal
        have old:=oldIds Var.work
        omega
      · change zeroState.nextObject=parameterIds Var.a at equal
        have old:=oldIds Var.a
        omega
      · change zeroState.nextObject=parameterIds Var.b at equal
        have old:=oldIds Var.b
        omega
      · change zeroState.nextObject=parameterIds Var.work at equal
        have old:=oldIds Var.work
        omega
      · rfl
    · intro v;exact il.bound
  have aw:=zeroFrame.well.objectIds _ _ ar.2.1
  have bw:=zeroFrame.well.objectIds _ _ br.2.1
  have ww:=zeroFrame.well.objectIds _ _ zeroed.2.1
  have coreSep : ∀v,workObj≠coreIds parameterIds zeroState.nextObject v ∧
      aObj≠coreIds parameterIds zeroState.nextObject v ∧ bObj≠coreIds parameterIds zeroState.nextObject v:=by
    intro v;cases v
    · exact separate Var.a
    · exact separate Var.b
    · exact separate Var.work
    · simp only [coreIds];omega
  have noDecrease : before.nextObject≤zeroState.nextObject:=by
    have old:=oldIds Var.work;rw [latestParameter];omega
  have sourceFrame : Frame before.nextObject before after [workObj]:=by
    refine ⟨afterW,?_,?_,?_,?_,?_,?_⟩
    · rw [di.nextObject];omega
    · rw [di.nextObject];omega
    · rw [di.nextScope,freshScope]
      have current:=zeroFrame.well.current
      rw [zeroFrame.scope,←ownerCurrent] at current
      omega
    · exact wa.1.trans work.1.symm
    · exact (declare_foreign iDeclared).trans zeroFrame.foreign
    · intro id old outside
      rw [di.outside id (by omega)]
      exact zeroFrame.objects id old (by simpa only [List.mem_singleton] using outside)
  have ai : ProductInner.Slice after aObj aSize aStart (fun k=>aData (aStart+k)):=
    ⟨ad,aa,fun k hk=>av k (by omega)⟩
  have bi : ProductInner.Slice after bObj bSize bStart (fun k=>bData (bStart+k)):=
    ⟨bd,ba,fun k hk=>bv k (by omega)⟩
  refine ⟨after,zeroState.nextObject,.cons zeroExec (.cons
    (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) iDeclared) .nil),
    ⟨wa,ai,bi,locals,coreSep,aShape,bShape,?_,?_,by omega,by omega,workBound,aDigits,bDigits,?_,by norm_num,afterW⟩,
    il,oldIds,sourceFrame,?_,?_⟩
  · rcases aDisjoint with no | low | high
    · exact Or.inl no
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr high)
  · rcases bDisjoint with no | low | high
    · exact Or.inl no
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr high)
  · intro k hk;rw [ZeroSlice.zeroData_inside _ _ _ _ hk];norm_num
  · intro k hk;have loaded:=word_load aa (by omega : aStart+k<aSize)
    simpa only [av k hk] using loaded
  · intro k hk;have loaded:=word_load ba (by omega : bStart+k<bSize)
    simpa only [bv k hk] using loaded

#print axioms actual_prefix
#print axioms zeroized_input
#print axioms prefix_execution
end RH080Next.FFTPV.MultiplyParameters
