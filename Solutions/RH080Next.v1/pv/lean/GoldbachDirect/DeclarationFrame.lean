import GoldbachDirect.SourceWellScoped

set_option autoImplicit false

namespace GoldbachDirect.SourceLocals

/-- Ordinary scalar-local declaration metadata and frame, independent of the
initializer's numerical meaning. Only the newly born allocation can change. -/
theorem declare_frame {F : Type} {before after : State F} {type : CType}
    {name : String} {value : Option Value}
    (declared : before.declare type name value = some after) :
    after.scope = before.scope ∧ after.nextScope = before.nextScope ∧
      after.nextObject = before.nextObject+1 ∧ after.mode = before.mode ∧
      (∀ id, id ≠ before.nextObject → after.objects id = before.objects id) := by
  cases width : type.byteSize with
  | none => simp [State.declare,width] at declared
  | some bytes =>
    cases fresh : before.objects before.nextObject with
    | some old => simp [State.declare,width,State.allocate,fresh] at declared
    | none =>
      cases value with
      | none =>
        simp [State.declare,width,State.allocate,fresh] at declared
        cases declared
        exact ⟨rfl,rfl,rfl,rfl,fun id different => by simp [different]⟩
      | some value =>
        simp only [State.declare,width,State.allocate,fresh,Option.isSome_none,Bool.false_eq_true,
          ↓reduceIte,Option.bind_some] at declared
        obtain ⟨_,mode,scope,nextScope,nextObject,frame⟩ := store_frame declared
        exact ⟨scope,nextScope,nextObject,mode,fun id different => by
          rw [frame id different]
          simp [different]⟩

theorem declare_read_old {F : Type} {before after : State F} {type : CType}
    {name : String} {value : Option Value} {pointer : Pointer}
    (declared : before.declare type name value = some after)
    (old : pointer.object ≠ before.nextObject) : after.load pointer = before.load pointer := by
  obtain ⟨_,_,_,mode,frame⟩ := declare_frame declared
  unfold State.load
  rw [frame pointer.object old]
  simp only [State.accessible,mode]
  rfl

theorem store_foreign {F : Type} {before after : State F} {pointer : Pointer} {value : Value}
    (written : before.store pointer value = some after) : after.foreign = before.foreign := by
  cases present : before.objects pointer.object with
  | none => simp [State.store,present] at written
  | some object =>
    cases width : pointer.element.byteSize with
    | none => simp [State.store,present,width] at written
    | some bytes =>
      cases converted : Value.convert pointer.element value with
      | none => simp [State.store,present,width,converted] at written
      | some result =>
        simp [State.store,present,width,converted] at written
        rcases written with ⟨_,rfl⟩
        rfl

theorem declare_foreign {F : Type} {before after : State F} {type : CType}
    {name : String} {value : Option Value}
    (declared : before.declare type name value = some after) : after.foreign = before.foreign := by
  cases width : type.byteSize with
  | none => simp [State.declare,width] at declared
  | some bytes =>
    cases fresh : before.objects before.nextObject with
    | some old => simp [State.declare,width,State.allocate,fresh] at declared
    | none =>
      cases value with
      | none =>
        simp [State.declare,width,State.allocate,fresh] at declared
        cases declared
        rfl
      | some value =>
        simp only [State.declare,width,State.allocate,fresh,Option.isSome_none,Bool.false_eq_true,
          ↓reduceIte,Option.bind_some] at declared
        have same := store_foreign declared
        exact same

theorem declare_environment {F : Type} {before after : State F} {type : CType}
    {name : String} {value : Option Value}
    (declared : before.declare type name value = some after) :
    after.environment = (name,⟨before.nextObject,0,type⟩)::before.environment := by
  cases width : type.byteSize with
  | none => simp [State.declare,width] at declared
  | some bytes =>
    cases fresh : before.objects before.nextObject with
    | some old => simp [State.declare,width,State.allocate,fresh] at declared
    | none =>
      cases value with
      | none =>
        simp [State.declare,width,State.allocate,fresh] at declared
        cases declared
        rfl
      | some value =>
        simp only [State.declare,width,State.allocate,fresh,Option.isSome_none,Bool.false_eq_true,
          ↓reduceIte,Option.bind_some] at declared
        exact (store_frame declared).1

end GoldbachDirect.SourceLocals

namespace GoldbachDirect.SourceLocals

inductive Declarations {F : Type} : State F → State F → Prop where
  | nil (state : State F) : Declarations state state
  | cons {before middle after : State F} {type : CType} {name : String} {value : Option Value}
      (declared : before.declare type name value = some middle)
      (tail : Declarations middle after) : Declarations before after

theorem Declarations.fields {F : Type} {before after : State F} (chain : Declarations before after) :
    before.nextObject ≤ after.nextObject ∧ after.scope = before.scope ∧
      after.nextScope = before.nextScope ∧ after.mode = before.mode ∧
      (∀ id, id < before.nextObject → after.objects id = before.objects id) := by
  induction chain with
  | nil state => exact ⟨le_refl _,rfl,rfl,rfl,fun _ _ => rfl⟩
  | @cons before middle after type name value declared tail ih =>
    obtain ⟨scope,nextScope,nextObject,mode,outside⟩ := declare_frame declared
    refine ⟨by omega,ih.2.1.trans scope,ih.2.2.1.trans nextScope,ih.2.2.2.1.trans mode,?_⟩
    intro id old
    rw [ih.2.2.2.2 id (by omega),outside id (by omega)]

end GoldbachDirect.SourceLocals
