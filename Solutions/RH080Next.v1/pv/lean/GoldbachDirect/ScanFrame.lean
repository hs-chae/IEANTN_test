import GoldbachDirect.SourceSlots

set_option autoImplicit false

namespace GoldbachDirect.ScanFrame
open SourceLocals Semantics

/-- The ordinary object and name frame of declaration-free source statements.
This records actual mutations; it asserts no numerical output property. -/
structure Frame {F : Type} (before after : State F) (writes : List Nat) : Prop where
  environment : after.environment = before.environment
  mode : after.mode = before.mode
  nextObject : after.nextObject = before.nextObject
  nextScope : before.nextScope ≤ after.nextScope
  origins : ∀ id object, after.objects id = some object →
    ∃ old, before.objects id = some old ∧ object.storage = old.storage
  outside : ∀ id, id ∉ writes → after.objects id = before.objects id

theorem Frame.refl {F : Type} (state : State F) (writes : List Nat) : Frame state state writes :=
  ⟨rfl,rfl,rfl,le_refl _,fun _ object present => ⟨object,present,rfl⟩,fun _ _ => rfl⟩

theorem Frame.trans {F : Type} {a b c : State F} {writes : List Nat}
    (first : Frame a b writes) (second : Frame b c writes) : Frame a c writes := by
  refine ⟨second.environment.trans first.environment,second.mode.trans first.mode,
    second.nextObject.trans first.nextObject,first.nextScope.trans second.nextScope,?_,?_⟩
  · intro id object present
    obtain ⟨middle,presentMiddle,sameMiddle⟩ := second.origins id object present
    obtain ⟨old,presentOld,sameOld⟩ := first.origins id middle presentMiddle
    exact ⟨old,presentOld,sameMiddle.trans sameOld⟩
  · intro id outside
    exact (second.outside id outside).trans (first.outside id outside)

theorem Frame.enter {F : Type} (state : State F) (writes : List Nat) :
    Frame state state.enterScope writes := by
  refine ⟨rfl,rfl,rfl,?_,fun _ object present => ⟨object,present,rfl⟩,fun _ _ => rfl⟩
  simp [State.enterScope]

theorem Frame.store {F : Type} {before after : State F} {pointer : Pointer} {value : Value}
    {writes : List Nat} (member : pointer.object ∈ writes)
    (written : before.store pointer value = some after) : Frame before after writes := by
  obtain ⟨environment,mode,_,nextScope,nextObject,outside⟩ := store_frame written
  refine ⟨environment,mode,nextObject,by rw [nextScope],?_,?_⟩
  · exact fun _ _ present => store_object_origin written present
  · intro id absent
    exact outside id (by intro same; exact absent (same ▸ member))

/-- Leaving a declaration-free block does not invalidate a pre-existing object:
its fresh scope number was absent before entering the block. -/
theorem Frame.close {F : Type} {before middle : State F} {writes : List Nat}
    (well : WellScoped before) (body : Frame before.enterScope middle writes) :
    Frame before {middle.leaveScope before.nextScope before.environment with scope := before.scope}
      writes := by
  have total := (Frame.enter before writes).trans body
  have objects : (middle.leaveScope before.nextScope before.environment).objects = middle.objects := by
    funext id
    cases present : middle.objects id with
    | none => simp [State.leaveScope,present]
    | some object =>
      obtain ⟨old,oldPresent,storage⟩ := total.origins id object present
      have different : object.storage ≠ .automatic before.nextScope := by
        intro same
        have bound := well.automatic id old before.nextScope oldPresent (storage.symm.trans same)
        omega
      simp [State.leaveScope,present,different]
  refine ⟨rfl,total.mode,total.nextObject,total.nextScope,?_,?_⟩
  · intro id object present
    change (middle.leaveScope before.nextScope before.environment).objects id = _ at present
    rw [objects] at present
    exact total.origins id object present
  · intro id outside
    change (middle.leaveScope before.nextScope before.environment).objects id = _
    rw [objects]
    exact total.outside id outside

theorem Frame.wellScoped {F : Type} {before after : State F} {writes : List Nat}
    (well : WellScoped before) (frame : Frame before after writes)
    (scope : after.scope < after.nextScope) : WellScoped after := by
  refine ⟨scope,?_,?_⟩
  · intro id object present
    obtain ⟨old,oldPresent,_⟩ := frame.origins id object present
    rw [frame.nextObject]
    exact well.objectIds id old oldPresent
  · intro id object owner present storage
    obtain ⟨old,oldPresent,same⟩ := frame.origins id object present
    have bound := well.automatic id old owner oldPresent (same.symm.trans storage)
    exact bound.trans_le frame.nextScope

theorem assignment_store {F : Type} {context : Context F} {before after : State F}
    {name : String} {expression : Expr} {pointer : Pointer} {value : Value}
    (closed : SourcePure.CallFree expression)
    (computed : PureEval.eval context before expression = some value)
    (named : before.environment.lookup name = some pointer)
    (run : Exec context before (.assign (.variable name) expression) .normal after) :
    before.store pointer value = some after := by
  cases run with
  | assign right left written =>
      obtain ⟨same,actual⟩ := PureEval.eval_sound right closed
      subst_vars
      have sameValue := Option.some.inj (actual.symm.trans computed)
      cases sameValue
      cases left with
      | «variable» found =>
          have samePointer := Option.some.inj (found.symm.trans named)
          cases samePointer
          exact written

/-- A uint64 store is determined by the actual C conversion of its RHS. -/
theorem store64_converted {F : Type} (state : State F) (pointer : Pointer) (value : Value)
    (type : pointer.element = .u64) (converted : Value.convert .u64 value =
      some (.integer (Kernel.integer64 (UInt64.ofNat 3)))) :
    state.store pointer value = state.store pointer (.integer (Kernel.integer64 (UInt64.ofNat 3))) := by
  unfold State.store
  simp only [type]
  rw [converted]
  simp only [Value.convert,CType.integer,Kernel.cast64_self]

theorem assignment_at {F : Type} {context : Context F} {before after : State F}
    {destination expression : Expr} {pointer : Pointer} {value : Value}
    (rightClosed : SourcePure.CallFree expression) (leftClosed : SourcePure.CallFree destination)
    (computed : PureEval.eval context before expression = some value)
    (placed : PureEval.place context before destination = some pointer)
    (run : Exec context before (.assign destination expression) .normal after) :
    before.store pointer value = some after := by
  cases run with
  | assign right left written =>
    obtain ⟨same,actual⟩ := PureEval.eval_sound right rightClosed
    subst_vars
    have valueSame := Option.some.inj (actual.symm.trans computed)
    cases valueSame
    obtain ⟨same,actual,_⟩ := PureEval.place_sound left leftClosed
    subst_vars
    have pointerSame := Option.some.inj (actual.symm.trans placed)
    cases pointerSame
    exact written

end GoldbachDirect.ScanFrame
