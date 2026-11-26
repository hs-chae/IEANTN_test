/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootAdd
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- The genuine function-owned i slot survives nested calls and loop-body
scopes. Its owner is not confused with the current block's scope. -/
structure Runtime {F : Type} (state : State F) (input : Input) (owner statusId indexId : Nat)
    (ids : Param → Nat) (data : Nat → Nat) (index : Nat) : Prop where
  view : ScaleView state input owner statusId ids data
  counter : Slot state indexId owner .u64 (.integer (integer64 index))
  lookup : state.environment.lookup "i"=some (scalarPointer indexId .u64)
  separate : input.layout.object≠indexId
  statusDifferent : statusId≠indexId
  paramsDifferent : ∀p,ids p≠indexId
  indexFresh : ids .root≤ indexId
  active : owner≤ state.scope

theorem Runtime.enter {F : Type} {state : State F} {input : Input} {owner statusId indexId index : Nat}
    {ids : Param → Nat} {data : Nat → Nat} (h : Runtime state input owner statusId indexId ids data index) :
    Runtime state.enterScope input owner statusId indexId ids data index := by
  refine ⟨⟨⟨h.view.params.array,h.view.params.locals.enter,h.view.params.separate,wellScoped_enter h.view.params.well⟩,
      ⟨h.view.status.storable,h.view.status.object⟩,h.view.statusLookup,h.view.statusSeparate⟩,
    ⟨h.counter.storable,h.counter.object⟩,h.lookup,h.separate,h.statusDifferent,h.paramsDifferent,h.indexFresh,?_⟩
  exact h.view.params.locals.bound.le

theorem Runtime.reframe {F : Type} {before after : State F} {input : Input} {owner statusId indexId index : Nat}
    {ids : Param → Nat} {old data : Nat → Nat} (h : Runtime before input owner statusId indexId ids old index)
    (view : ScaleView after input owner statusId ids data)
    (environment : after.environment=before.environment) (scope : after.scope=before.scope)
    (objects : ∀id,id< before.nextObject → id≠input.layout.object → after.objects id=before.objects id) :
    Runtime after input owner statusId indexId ids data index := by
  refine ⟨view,⟨h.counter.storable,?_⟩,?_,h.separate,h.statusDifferent,h.paramsDifferent,h.indexFresh,?_⟩
  · rw [objects _ (h.view.params.well.objectIds _ _ h.counter.object) h.separate.symm];exact h.counter.object
  · rw [environment];exact h.lookup
  · rw [scope];exact h.active

def indexDeclaration : Stmt:=.declare .u64 "i" (some (.literal (.integer 1 "ULL")))
def indexIncrement : Stmt:=.assign (.variable "i") (.paren (.binary .add (.variable "i") (.literal (.integer 1 "ULL"))))

/-- The actual i=1 application declaration, after all real nested setup calls.
The identity is taken from the returned heap, with its real function owner. -/
theorem index_declaration_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner statusId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ScaleView before input owner statusId ids data) (scope : before.scope=owner) :
    ∃after,Exec context before indexDeclaration .normal after ∧
      Every context before indexDeclaration .normal after ∧
      Runtime after input owner statusId before.nextObject ids data 1 ∧ after.scope=owner := by
  have one:=ZeroFrame.u64_storable 1 (by norm_num)
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists h.params.well .u64 "i" (.integer (integer64 1)) one
  have init:=declare_storable one (convert64 1 (by norm_num)) declared
  have locals:=ApplicationBirthFrame.locals_declare_old h.params.well h.params.locals
    (by intro p;cases p <;> decide) init
  have array:=ApplicationBirthFrame.array_declare_old h.params.well h.params.array init
  have status:=ApplicationBirthFrame.slot_declare_old h.params.well h.status init
  have oldArray:=h.params.well.objectIds _ _ h.params.array.2.1
  have oldStatus:=h.params.well.objectIds _ _ h.status.object
  have paramsOld (p : Param) : ids p< before.nextObject:=h.params.well.objectIds _ _ (h.params.locals.slots p).object
  have actualScope : after.scope=owner:=init.scope.trans scope
  have statusLookup : after.environment.lookup "status"=some (scalarPointer statusId .u64):=by
    rw [init.environment];simpa [List.lookup] using h.statusLookup
  have indexLookup : after.environment.lookup "i"=some (scalarPointer before.nextObject .u64):=by simp [init.environment,List.lookup]
  have counter : Slot after before.nextObject owner .u64 (.integer (integer64 1)):=by rw [←scope];exact init.slot
  have run : Exec context before indexDeclaration .normal after:=.declareSome
    (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl)) declared
  exact ⟨after,run,every_pure (by simp [indexDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) run,
    ⟨⟨⟨array,locals,h.params.separate,wellScoped_declare h.params.well declared⟩,status,statusLookup,h.statusSeparate⟩,
      counter,indexLookup,by omega,by omega,(by intro p;have hp:=paramsOld p;omega),(by have hp:=paramsOld .root;omega),actualScope.ge⟩,actualScope⟩

/-- Actual final source assignment i=i+1, including typed no-wrap arithmetic
and preservation of the enclosing function's status and pointer bindings. -/
theorem index_increment_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner statusId indexId index : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data index) (bound : index+1<2^64) :
    ∃after,Exec context before indexIncrement .normal after ∧
      Every context before indexIncrement .normal after ∧
      Runtime after input owner statusId indexId ids data (index+1) ∧ after.scope=before.scope ∧
      ApplicationBirthFrame.Frame (ids .root) before after [input.layout.object] := by
  have storable:=ZeroFrame.u64_storable (index+1) bound
  obtain ⟨after,stored⟩:=IncrementSource.slot_store_exists h.counter (.integer (integer64 (index+1))) storable
  have run : Exec context before indexIncrement .normal after:=.assign
    (.paren (.binaryLR (.variable h.lookup h.counter.read)
      (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
      (by simp only [binary,binary64_add index 1 (by omega) (by norm_num) bound,Option.map_some])))
    (.variable h.lookup) stored
  have fields:=SourceLocals.store_frame stored
  have locals:=ApplicationBirthFrame.locals_store_other h.view.params.locals h.paramsDifferent stored
  have status:=ApplicationBirthFrame.slot_store_other h.view.status h.statusDifferent stored
  have counter:=h.counter.store storable stored
  have array : WordArrayRep after input.layout.object input.layout.size data:=
    ⟨fields.2.1.trans h.view.params.array.1,
      (fields.2.2.2.2.2 _ h.separate).trans h.view.params.array.2.1,h.view.params.array.2.2⟩
  have well:=wellScoped_store h.view.params.well stored
  have oldRoot:=h.view.params.well.objectIds _ _ (h.view.params.locals.slots Param.root).object
  have birthFrame:=ApplicationBirthFrame.store_frame (ids .root) [input.layout.object] h.view.params.well oldRoot.le
    (Or.inr h.indexFresh) stored
  exact ⟨after,run,every_pure (by simp [indexIncrement,PureDeterminism.Simple,SourcePure.CallFree]) run,⟨⟨⟨array,locals,h.view.params.separate,well⟩,status,by rw [fields.1];exact h.view.statusLookup,h.view.statusSeparate⟩,
    counter,by rw [fields.1];exact h.lookup,h.separate,h.statusDifferent,h.paramsDifferent,h.indexFresh,by rw [fields.2.2.1];exact h.active⟩,fields.2.2.1,birthFrame⟩

#print axioms Runtime.enter
#print axioms index_declaration_execution
#print axioms index_increment_execution
end RH080Next.FFTPV.RootSource
