import GoldbachDirect.SourceWellScoped
import GoldbachDirect.PureEval
import GoldbachDirect.SourceControl

set_option autoImplicit false

namespace GoldbachDirect.SourceSlots
open Kernel SourceLocals Semantics

def object64 (owner : Nat) (value : UInt64) : Object :=
  ⟨8,true,.automatic owner,fun offset => if offset = 0 then some (.integer (integer64 value)) else none⟩

def Slot {F : Type} (state : State F) (id owner : Nat) (value : UInt64) : Prop :=
  state.objects id = some (object64 owner value)

theorem slot_read {F : Type} {state : State F} {id owner : Nat} {value : UInt64}
    (slot : Slot state id owner value) :
    state.load (local64 id) = some (.integer (integer64 value)) := by
  change state.objects id = some (object64 owner value) at slot
  simp [State.load,local64,object64,State.accessible,CType.byteSize,slot,
    Value.convert,CType.integer]
  exact stored_u64_width value.toNat

theorem slot_store {F : Type} {before after : State F} {id owner : Nat} {old value : UInt64}
    (slot : Slot before id owner old)
    (written : before.store (local64 id) (.integer (integer64 value)) = some after) :
    Slot after id owner value := by
  simp [State.store,local64,show before.objects id = some (object64 owner old) from slot,
    object64,State.accessible,CType.byteSize,Value.convert,CType.integer] at written
  cases written
  unfold Slot object64
  simp only [↓reduceIte,Option.some.injEq,Object.mk.injEq]
  refine ⟨trivial,trivial,trivial,?_⟩
  funext offset
  by_cases zero : offset = 0
  · simp [zero]
  · simp [zero]

theorem slot_declare64 {F : Type} {before after : State F} (name : String) (value : UInt64)
    (original : Value) (converted : Value.convert .u64 original = some (.integer (integer64 value)))
    (declared : before.declare .u64 name (some original) = some after) :
    Slot after before.nextObject before.scope value ∧
      after.scope = before.scope ∧ after.nextScope = before.nextScope := by
  cases fresh : before.objects before.nextObject with
  | some old => simp [State.declare,State.allocate,fresh] at declared
  | none =>
      simp [State.declare,State.allocate,fresh,State.store,State.accessible,
        CType.byteSize,converted] at declared
      cases declared
      refine ⟨?_,rfl,rfl⟩
      unfold Slot object64
      simp only [↓reduceIte]

/-- A fixed family of actual addressable C locals. All cells belong to the
same already-entered function scope. No loop result or arithmetic fact occurs
in this representation predicate. -/
structure Locals {F I : Type} (state : State F) (names : I → String)
    (ids : I → Nat) (owner : Nat) (values : I → UInt64) : Prop where
  lookup : ∀ i, state.environment.lookup (names i) = some (local64 (ids i))
  slots : ∀ i, Slot state (ids i) owner (values i)
  distinct : Function.Injective ids
  bound : owner < state.nextScope

theorem Locals.read {F I : Type} {state : State F} {names : I → String} {ids : I → Nat}
    {owner : Nat} {values : I → UInt64} (locals : Locals state names ids owner values) (i : I) :
    state.load (local64 (ids i)) = some (.integer (integer64 (values i))) := slot_read (locals.slots i)

theorem Locals.enter {F I : Type} {state : State F} {names : I → String} {ids : I → Nat}
    {owner : Nat} {values : I → UInt64} (locals : Locals state names ids owner values) :
    Locals state.enterScope names ids owner values := by
  refine ⟨locals.lookup,locals.slots,locals.distinct,?_⟩
  simp only [State.enterScope]
  have := locals.bound
  omega

theorem Locals.store {F I : Type} [DecidableEq I] {before after : State F}
    {names : I → String} {ids : I → Nat} {owner : Nat} {values : I → UInt64}
    (locals : Locals before names ids owner values) (i : I) (value : UInt64)
    (written : before.store (local64 (ids i)) (.integer (integer64 value)) = some after) :
    Locals after names ids owner (Function.update values i value) := by
  obtain ⟨environment,_,_,nextScope,_,objects⟩ := store_frame written
  refine ⟨by simpa [environment] using locals.lookup,?_,locals.distinct,by simpa [nextScope] using locals.bound⟩
  intro j
  by_cases same : j = i
  · subst j
    simpa using slot_store (locals.slots i) written
  · rw [Function.update_of_ne same]
    exact (objects (ids j) (by intro eq; exact same (locals.distinct eq))).trans (locals.slots j)

theorem Locals.leave {F I : Type} {state : State F} {names : I → String} {ids : I → Nat}
    {owner scope : Nat} {values : I → UInt64} (locals : Locals state names ids owner values)
    (different : scope ≠ owner) (environment : List (String × Pointer))
    (lookup : ∀ i, environment.lookup (names i) = some (local64 (ids i))) (restore : Nat) :
    Locals {state.leaveScope scope environment with scope := restore} names ids owner values := by
  refine ⟨lookup,?_,locals.distinct,locals.bound⟩
  intro i
  change ((state.objects (ids i)).map _) = _
  rw [locals.slots i]
  simp [object64,different.symm]

theorem Locals.assign {F I : Type} [DecidableEq I] {context : Context F}
    {before after : State F} {names : I → String} {ids : I → Nat} {owner : Nat}
    {values : I → UInt64} (locals : Locals before names ids owner values) (i : I)
    (expression : Expr) (closed : SourcePure.CallFree expression) (value : UInt64)
    (computed : PureEval.eval context before expression = some (.integer (integer64 value)))
    (run : Exec context before (.assign (.variable (names i)) expression) .normal after) :
    Locals after names ids owner (Function.update values i value) := by
  cases run with
  | assign right left written =>
      obtain ⟨stateSame,actual⟩ := PureEval.eval_sound right closed
      subst_vars
      have same := Option.some.inj (actual.symm.trans computed)
      cases same
      cases left with
      | «variable» found =>
          have pointerSame := Option.some.inj (found.symm.trans (locals.lookup i))
          cases pointerSame
          exact locals.store i value written

theorem assign_block_normal {F : Type} {context : Context F} {before after : State F}
    {name : String} {expression : Expr} {flow : Flow}
    (run : Exec context before (.block [.assign (.variable name) expression]) flow after) :
    flow = .normal := by
  apply SourceControl.block_normal run
  intro statement member before after flow step
  simp only [List.mem_singleton] at member
  subst statement
  exact SourceControl.assign_normal step

theorem Locals.assign_block {F I : Type} [DecidableEq I] {context : Context F}
    {before after : State F} {names : I → String} {ids : I → Nat} {owner : Nat}
    {values : I → UInt64} (locals : Locals before names ids owner values) (i : I)
    (expression : Expr) (closed : SourcePure.CallFree expression) (value : UInt64)
    (computed : PureEval.eval context before.enterScope expression = some (.integer (integer64 value)))
    (run : Exec context before (.block [.assign (.variable (names i)) expression]) .normal after) :
    Locals after names ids owner (Function.update values i value) := by
  cases run with
  | block entered body finished =>
      subst_vars
      obtain ⟨middle,assignment,rest⟩ := SourceControl.list_head body (by
        intro before after flow step
        exact SourceControl.assign_normal step)
      cases rest
      have next := locals.enter.assign i expression closed value computed assignment
      exact next.leave (by change before.nextScope ≠ owner; have := locals.bound; omega)
        before.environment locals.lookup before.scope

theorem declared_of_eval {F : Type} {context : Context F} {before after : State F}
    {type : CType} {name : String} {expression : Expr} {value : Value}
    (closed : SourcePure.CallFree expression)
    (computed : PureEval.eval context before expression = some value)
    (run : Exec context before (.declare type name (some expression)) .normal after) :
    before.declare type name (some value) = some after := by
  cases run with
  | declareSome evaluated declared =>
      obtain ⟨same,actual⟩ := PureEval.eval_sound evaluated closed
      subst_vars
      have sameValue := Option.some.inj (actual.symm.trans computed)
      cases sameValue
      exact declared

end GoldbachDirect.SourceSlots
