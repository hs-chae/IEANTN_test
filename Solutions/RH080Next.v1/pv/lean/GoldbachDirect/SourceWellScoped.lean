import GoldbachDirect.SourceLocals
import GoldbachDirect.PlatformMemory

set_option autoImplicit false

namespace GoldbachDirect.SourceLocals

/-- Ordinary validity of the language's allocation/scope names. It states no
program result, source path, numerical data or call applicability. -/
structure WellScoped {F : Type} (state : State F) : Prop where
  current : state.scope < state.nextScope
  objectIds : ∀ id object, state.objects id = some object → id < state.nextObject
  automatic : ∀ id object scope, state.objects id = some object →
    object.storage = .automatic scope → scope < state.nextScope

theorem wellScoped_environment {F : Type} {state : State F} (well : WellScoped state)
    (environment : List (String × Pointer)) : WellScoped {state with environment} :=
  ⟨well.current,well.objectIds,well.automatic⟩

theorem wellScoped_scope {F : Type} {state : State F} (well : WellScoped state)
    {scope : Nat} (bound : scope < state.nextScope) : WellScoped {state with scope} :=
  ⟨bound,well.objectIds,well.automatic⟩

theorem wellScoped_enter {F : Type} {state : State F} (well : WellScoped state) :
    WellScoped state.enterScope := by
  refine ⟨by simp [State.enterScope],?_,?_⟩
  · exact well.objectIds
  · intro id object scope present storage
    have := well.automatic id object scope present storage
    simp only [State.enterScope]
    omega

theorem wellScoped_allocate {F : Type} {before after : State F} {pointer : Pointer}
    {storage : Storage} {extent : Nat} {cells : Nat → Option Value}
    (well : WellScoped before)
    (scope : ∀ owner, storage = .automatic owner → owner < before.nextScope)
    (born : before.allocate storage extent cells = some (pointer,after)) : WellScoped after := by
  unfold State.allocate at born
  split_ifs at born
  cases Option.some.inj born
  refine ⟨well.current,?_,?_⟩
  · intro id object present
    by_cases same : id = before.nextObject
    · subst id
      simp only [↓reduceIte, Option.some.injEq] at present
      cases present
      simp
    · have old := well.objectIds id object (by simpa [same] using present)
      simp only
      omega
  · intro id object owner present automatic
    by_cases same : id = before.nextObject
    · subst id
      simp only [↓reduceIte, Option.some.injEq] at present
      cases present
      exact scope owner automatic
    · exact well.automatic id object owner (by simpa [same] using present) automatic

theorem store_object_origin {F : Type} {before after : State F} {pointer : Pointer} {value : Value}
    (written : before.store pointer value = some after) {id : Nat} {object : Object}
    (present : after.objects id = some object) :
    ∃ old, before.objects id = some old ∧ object.storage = old.storage := by
  cases target : before.objects pointer.object with
  | none => simp [State.store,target] at written
  | some old =>
      cases width : pointer.element.byteSize with
      | none => simp [State.store,target,width] at written
      | some bytes =>
          cases converted : Value.convert pointer.element value with
          | none => simp [State.store,target,width,converted] at written
          | some result =>
              simp [State.store,target,width,converted] at written
              rcases written with ⟨_,rfl⟩
              by_cases same : id = pointer.object
              · subst id
                simp only [↓reduceIte,Option.some.injEq] at present
                cases present
                exact ⟨old,target,rfl⟩
              · exact ⟨object,by simpa [same] using present,rfl⟩

theorem wellScoped_store {F : Type} {before after : State F} {pointer : Pointer} {value : Value}
    (well : WellScoped before) (written : before.store pointer value = some after) :
    WellScoped after := by
  obtain ⟨_,_,scope,nextScope,nextObject,_⟩ := store_frame written
  refine ⟨by rw [scope,nextScope]; exact well.current,?_,?_⟩
  · intro id object present
    obtain ⟨old,oldPresent,_⟩ := store_object_origin written present
    rw [nextObject]
    exact well.objectIds id old oldPresent
  · intro id object owner present storage
    obtain ⟨old,oldPresent,sameStorage⟩ := store_object_origin written present
    rw [nextScope]
    exact well.automatic id old owner oldPresent (sameStorage.symm.trans storage)

theorem leave_object_origin {F : Type} {state : State F} (scope : Nat)
    (environment : List (String × Pointer)) {id : Nat} {object : Object}
    (present : (state.leaveScope scope environment).objects id = some object) :
    ∃ old, state.objects id = some old ∧ object.storage = old.storage := by
  cases original : state.objects id with
  | none => simp [State.leaveScope,original] at present
  | some old =>
      simp only [State.leaveScope,original,Option.map_some,Option.some.injEq] at present
      refine ⟨old,rfl,?_⟩
      split_ifs at present <;> cases present <;> rfl

theorem wellScoped_leave {F : Type} {state : State F} (well : WellScoped state)
    (scope : Nat) (environment : List (String × Pointer)) :
    WellScoped (state.leaveScope scope environment) := by
  refine ⟨well.current,?_,?_⟩
  · intro id object present
    obtain ⟨old,oldPresent,_⟩ := leave_object_origin scope environment present
    exact well.objectIds id old oldPresent
  · intro id object owner present storage
    obtain ⟨old,oldPresent,sameStorage⟩ := leave_object_origin scope environment present
    exact well.automatic id old owner oldPresent (sameStorage.symm.trans storage)

theorem wellScoped_declare {F : Type} {before after : State F} {type : CType}
    {name : String} {initial : Option Value} (well : WellScoped before)
    (declared : before.declare type name initial = some after) : WellScoped after := by
  cases size : type.byteSize with
  | none => simp [State.declare,size] at declared
  | some bytes =>
      cases born : before.allocate (.automatic before.scope) bytes with
      | none => simp [State.declare,size,born] at declared
      | some pair =>
          rcases pair with ⟨pointer,allocated⟩
          have allocatedWell := wellScoped_allocate well (fun owner same => by
            cases same
            exact well.current) born
          cases initial with
          | none =>
              simp [State.declare,size,born] at declared
              cases declared
              exact wellScoped_environment allocatedWell _
          | some value =>
              simp [State.declare,size,born] at declared
              exact wellScoped_store (wellScoped_environment allocatedWell _) declared

theorem wellScoped_release {F : Type} {before after : State F} {pointer : Pointer}
    (well : WellScoped before) (released : PlatformMemory.release before pointer = some after) :
    WellScoped after := by
  unfold PlatformMemory.release at released
  cases present : before.objects pointer.object with
  | none => simp [present] at released
  | some old =>
      simp only [present] at released
      split_ifs at released
      cases Option.some.inj released
      refine ⟨well.current,?_,?_⟩
      · intro id object found
        by_cases same : id = pointer.object
        · subst id
          simp only [↓reduceIte,Option.some.injEq] at found
          cases found
          exact well.objectIds _ _ present
        · exact well.objectIds _ _ (by simpa [same] using found)
      · intro id object owner found storage
        by_cases same : id = pointer.object
        · subst id
          simp only [↓reduceIte,Option.some.injEq] at found
          cases found
          exact well.automatic _ _ _ present storage
        · exact well.automatic _ _ _ (by simpa [same] using found) storage

theorem wellScoped_platform_call {F : Type} {operation : Semantics.External}
    {arguments : List Value} {before after : State F} {result : Value}
    (well : WellScoped before)
    (run : PlatformMemory.Call F operation arguments before result after) : WellScoped after := by
  cases run with
  | mallocFailure => exact well
  | mallocSuccess _ _ _ _ _ _ born =>
      exact wellScoped_allocate well (by intro owner impossible; cases impossible) born
  | callocFailure => exact well
  | callocSuccess _ _ _ _ _ _ _ _ _ _ born =>
      exact wellScoped_allocate well (by intro owner impossible; cases impossible) born
  | freeNull => exact well
  | freeObject _ _ _ released => exact wellScoped_release well released

end GoldbachDirect.SourceLocals
