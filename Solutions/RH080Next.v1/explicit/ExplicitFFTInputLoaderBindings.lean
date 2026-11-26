/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTInputAST
import FFTInputCellBounds
import FFTEncodedSelectorSource
import ExplicitFFTRootEvery
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

inductive Parameter where | data | n | j deriving DecidableEq
inductive Temporary where | e | value | sign | scaled | p deriving DecidableEq
abbrev Var:=Parameter⊕Temporary

def parameterName : Parameter → String | .data=>"data" | .n=>"n" | .j=>"j"
def temporaryName : Temporary → String | .e=>"e" | .value=>"value" | .sign=>"sign" | .scaled=>"scaled" | .p=>"p"
def varName : Var → String | .inl p=> parameterName p | .inr t=> temporaryName t

def varType : Var → CType | .inl .data | .inr .p=>.pointer .u64 | _=>.u64

def localIndex : Temporary → Nat | .e=>0 | .value=>1 | .sign=>2 | .scaled=>3 | .p=>4

def Active (count : Nat) : Var → Prop | .inl _=> True | .inr t=> localIndex t< count

def owner (functionOwner blockOwner : Nat) : Var → Nat | .inl _=> functionOwner | .inr _=> blockOwner

theorem name_injective : Function.Injective varName:=by
  intro a b h
  cases a with
  | inl a=> cases b with
    | inl b=> cases a <;> cases b <;> simp_all [varName,parameterName]
    | inr b=> cases a <;> cases b <;> simp_all [varName,parameterName,temporaryName]
  | inr a=> cases b with
    | inl b=> cases a <;> cases b <;> simp_all [varName,parameterName,temporaryName]
    | inr b=> cases a <;> cases b <;> simp_all [varName,temporaryName]

theorem index_injective : Function.Injective localIndex:=by
  intro a b h;cases a <;> cases b <;> simp_all [localIndex]

theorem active_step {count : Nat} {next : Temporary} (hn : localIndex next=count) (v : Var) :
    Active (count+1) v ↔ v=.inr next ∨ Active count v:=by
  cases v with
  | inl p=> simp [Active]
  | inr t=>
    simp only [Active,Sum.inr.injEq]
    constructor
    · intro h;by_cases old : localIndex t< count
      · exact Or.inr old
      · exact Or.inl (index_injective (by omega))
    · intro h;rcases h with rfl|old <;> omega

/-- Progressive actual application bindings. Persistent main variables belong
to their function, and a temporary exists only after its real block declaration. -/
structure PartialBindings {F : Type} (state : State F) (count functionOwner blockOwner : Nat)
    (ids : Var → Nat) (values : Var → Value) : Prop where
  lookup : ∀v,Active count v → state.environment.lookup (varName v)=some (scalarPointer (ids v) (varType v))
  slots : ∀v,Active count v → Slot state (ids v) (owner functionOwner blockOwner v) (varType v) (values v)
  distinct : ∀v w,Active count v → Active count w → ids v=ids w → v=w
  bound : ∀v,Active count v → owner functionOwner blockOwner v< state.nextScope

theorem PartialBindings.read {F : Type} {state : State F} {count fo bo : Nat} {ids : Var → Nat} {values : Var → Value}
    (h : PartialBindings state count fo bo ids values) (v : Var) (hv : Active count v) :
    state.load (scalarPointer (ids v) (varType v))=some (values v):=(h.slots v hv).read

theorem PartialBindings.declare_next {F : Type} {before after : State F} {count fo bo : Nat}
    {ids : Var → Nat} {values : Var → Value} {next : Temporary}
    (h : PartialBindings before count fo bo ids values) (well : WellScoped before) (scope : before.scope=bo)
    (index : localIndex next=count)
    (d : Declaration before after (temporaryName next) (varType (.inr next)) (values (.inr next))) :
    PartialBindings after (count+1) fo bo (Function.update ids (.inr next) before.nextObject) values:=by
  have oldActive (v : Var) (hv : Active (count+1) v) (different : v≠.inr next) : Active count v:=
    ((active_step index v).mp hv).resolve_left different
  have oldNe (v : Var) (hv : Active count v) : v≠.inr next:=by
    intro same;subst v;change localIndex next< count at hv;omega
  refine ⟨?_,?_,?_,?_⟩
  · intro v hv
    by_cases same : v=.inr next
    · subst v;rw [Function.update_self,d.environment];simp [varName,List.lookup]
    · have names : varName v≠temporaryName next:=by intro eq;exact same (name_injective eq)
      rw [Function.update_of_ne same,d.environment]
      simpa [List.lookup,show (varName v==temporaryName next)=false from by simp [names]] using h.lookup v (oldActive v hv same)
  · intro v hv
    by_cases same : v=.inr next
    · subst v;rw [Function.update_self];simpa only [owner,scope] using d.slot
    · rw [Function.update_of_ne same]
      exact ApplicationBirthFrame.slot_declare_old well (h.slots v (oldActive v hv same)) d
  · intro v w hv hw equal
    by_cases vn : v=.inr next
    · subst v
      by_cases wn : w=.inr next
      · exact wn.symm
      · have bound:=well.objectIds _ _ (h.slots w (oldActive w hw wn)).object
        simp only [Function.update_self,Function.update_of_ne wn] at equal;omega
    · by_cases wn : w=.inr next
      · subst w
        have bound:=well.objectIds _ _ (h.slots v (oldActive v hv vn)).object
        simp only [Function.update_self,Function.update_of_ne vn] at equal;omega
      · simp only [Function.update_of_ne vn,Function.update_of_ne wn] at equal
        exact h.distinct v w (oldActive v hv vn) (oldActive w hw wn) equal
  · intro v hv;rw [d.nextScope]
    by_cases same : v=.inr next
    · subst v;simpa only [owner,scope] using well.current
    · exact h.bound v (oldActive v hv same)

theorem PartialBindings.store {F : Type} {before after : State F} {count fo bo : Nat}
    {ids : Var → Nat} {values : Var → Value} (h : PartialBindings before count fo bo ids values)
    (v : Var) (hv : Active count v) (value : Value) (storable : Storable (varType v) value)
    (written : before.store (scalarPointer (ids v) (varType v)) value=some after) :
    PartialBindings after count fo bo ids (Function.update values v value):=by
  have fields:=SourceLocals.store_frame written
  refine ⟨by rw [fields.1];exact h.lookup,?_,h.distinct,?_⟩
  · intro u hu
    by_cases same : u=v
    · subst u;simpa using (h.slots v hv).store storable written
    · rw [Function.update_of_ne same]
      apply ApplicationBirthFrame.slot_store_other (h.slots u hu) _ written
      intro eq;exact same (h.distinct u v hu hv eq)
  · intro u hu;rw [fields.2.2.2.1];exact h.bound u hu

theorem PartialBindings.store_other {F : Type} {before after : State F} {count fo bo : Nat}
    {ids : Var → Nat} {values : Var → Value} {pointer : Pointer} {value : Value}
    (h : PartialBindings before count fo bo ids values) (different : ∀v,Active count v → ids v≠pointer.object)
    (written : before.store pointer value=some after) : PartialBindings after count fo bo ids values:=by
  have fields:=SourceLocals.store_frame written
  exact ⟨by rw [fields.1];exact h.lookup,
    fun v hv=> ApplicationBirthFrame.slot_store_other (h.slots v hv) (different v hv) written,h.distinct,
    fun v hv=> by rw [fields.2.2.2.1];exact h.bound v hv⟩

theorem PartialBindings.enter {F : Type} {before : State F} {count fo bo : Nat}
    {ids : Var → Nat} {values : Var → Value} (h : PartialBindings before count fo bo ids values) :
    PartialBindings before.enterScope count fo bo ids values:=
  ⟨h.lookup,(fun v hv=>⟨(h.slots v hv).storable,(h.slots v hv).object⟩),h.distinct,
    fun v hv=> by have hb:=h.bound v hv;change owner fo bo v< before.nextScope+1;omega⟩

/-- Application helper calls restore the source environment and preserve actual
old scalar objects. Monotone clocks preserve each declared variable's lifetime. -/
theorem PartialBindings.after_call {F : Type} {before after : State F} {count fo bo : Nat}
    {ids : Var → Nat} {values : Var → Value} {writes : List Nat}
    (h : PartialBindings before count fo bo ids values) (well : WellScoped before)
    (frame : MultiplyCall.CallerFrame before after writes)
    (different : ∀v,Active count v → ids v∉writes) : PartialBindings after count fo bo ids values:=by
  refine ⟨by rw [frame.environment];exact h.lookup,?_,h.distinct,?_⟩
  · intro v hv
    refine ⟨(h.slots v hv).storable,?_⟩
    rw [frame.frame.outside _ (well.objectIds _ _ (h.slots v hv).object) (different v hv)]
    exact (h.slots v hv).object
  · intro v hv;exact lt_of_lt_of_le (h.bound v hv) frame.frame.nextScope

#print axioms PartialBindings.declare_next
#print axioms PartialBindings.store
#print axioms PartialBindings.after_call
end RH080Next.FFTPV.InputLoader
