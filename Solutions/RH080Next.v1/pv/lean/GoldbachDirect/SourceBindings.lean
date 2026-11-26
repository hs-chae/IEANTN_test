import GoldbachDirect.SourceScalarSlots
import GoldbachDirect.ScanFrame

set_option autoImplicit false

namespace GoldbachDirect.SourceBindings
open Semantics SourceScalarSlots SourceLocals

/-- Ordinary initialized application locals of their actual C types. Each
allocation identity is distinct, and belongs to the existing function scope. -/
structure Locals {F I : Type} (state : State F) (names : I → String) (types : I → CType)
    (ids : I → Nat) (owner : Nat) (values : I → Value) : Prop where
  lookup : ∀ i, state.environment.lookup (names i) = some (scalarPointer (ids i) (types i))
  slots : ∀ i, Slot state (ids i) owner (types i) (values i)
  distinct : Function.Injective ids
  bound : owner < state.nextScope

theorem Locals.read {F I : Type} {state : State F} {names : I → String} {types : I → CType}
    {ids : I → Nat} {owner : Nat} {values : I → Value}
    (locals : Locals state names types ids owner values) (i : I) :
    state.load (scalarPointer (ids i) (types i)) = some (values i) := (locals.slots i).read

theorem Locals.enter {F I : Type} {state : State F} {names : I → String} {types : I → CType}
    {ids : I → Nat} {owner : Nat} {values : I → Value}
    (locals : Locals state names types ids owner values) :
    Locals state.enterScope names types ids owner values := by
  refine ⟨locals.lookup,(fun i => ⟨(locals.slots i).storable,(locals.slots i).object⟩),locals.distinct,?_⟩
  have := locals.bound
  simp only [State.enterScope]
  omega

theorem Locals.store {F I : Type} [DecidableEq I] {before after : State F}
    {names : I → String} {types : I → CType} {ids : I → Nat} {owner : Nat} {values : I → Value}
    (locals : Locals before names types ids owner values) (i : I) (value : Value)
    (storable : Storable (types i) value)
    (written : before.store (scalarPointer (ids i) (types i)) value = some after) :
    Locals after names types ids owner (Function.update values i value) := by
  obtain ⟨environment,_,_,nextScope,_,outside⟩ := store_frame written
  refine ⟨by simpa [environment] using locals.lookup,?_,locals.distinct,by simpa [nextScope] using locals.bound⟩
  intro j
  by_cases same : j=i
  · subst j
    simpa using (locals.slots i).store storable written
  · rw [Function.update_of_ne same]
    refine ⟨(locals.slots j).storable,?_⟩
    rw [outside (ids j) (by intro eq; exact same (locals.distinct eq))]
    exact (locals.slots j).object

theorem Locals.leave {F I : Type} {state : State F} {names : I → String} {types : I → CType}
    {ids : I → Nat} {owner scope : Nat} {values : I → Value}
    (locals : Locals state names types ids owner values) (different : scope ≠ owner)
    (environment : List (String × Pointer))
    (lookup : ∀ i, environment.lookup (names i) = some (scalarPointer (ids i) (types i))) (restore : Nat) :
    Locals {state.leaveScope scope environment with scope:=restore} names types ids owner values := by
  refine ⟨lookup,?_,locals.distinct,locals.bound⟩
  intro i
  refine ⟨(locals.slots i).storable,?_⟩
  change ((state.objects (ids i)).map _) = _
  rw [(locals.slots i).object]
  simp [scalarObject,different.symm]

/-- Normalizing a RHS by its actual declared C conversion changes no store. -/
theorem store_converted {F : Type} (state : State F) (pointer : Pointer) (original value : Value)
    (converted : Value.convert pointer.element original = some value)
    (storable : Storable pointer.element value) :
    state.store pointer original = state.store pointer value := by
  unfold State.store
  rw [converted,storable.converted]

theorem Locals.assign {F I : Type} [DecidableEq I] {context : Context F} {before after : State F}
    {names : I → String} {types : I → CType} {ids : I → Nat} {owner : Nat} {values : I → Value}
    (locals : Locals before names types ids owner values) (i : I)
    (expression : Expr) (closed : SourcePure.CallFree expression) (original value : Value)
    (computed : PureEval.eval context before expression = some original)
    (converted : Value.convert (types i) original = some value) (storable : Storable (types i) value)
    (run : Exec context before (.assign (.variable (names i)) expression) .normal after) :
    Locals after names types ids owner (Function.update values i value) := by
  have written := ScanFrame.assignment_store closed computed (locals.lookup i) run
  rw [store_converted before _ original value converted storable] at written
  exact locals.store i value storable written

end GoldbachDirect.SourceBindings
