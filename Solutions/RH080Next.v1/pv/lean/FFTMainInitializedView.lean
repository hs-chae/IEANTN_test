/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainAllocationFour
import FFTZeroRawFullFrame
import FFTRecursiveBindingsFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

abbrev MainVar := Option Role

def variableName : MainVar → String | none=>"n" | some r=>name r
def variableType : MainVar → CType | none=>.u64 | some _=>.pointer .u64
def variableId (nId : Nat) (ids : Role → Nat) : MainVar → Nat | none=>nId | some r=>ids r
def variableValue (n : Nat) (objects : Role → Nat) : MainVar → Value
  | none=>.integer (integer64 n) | some r=>.pointer (wordPointer (objects r) 0)

theorem all_roles (r : Role) : r∈[.output,.work,.twiddle,.data] := by cases r <;> simp

theorem View.locals {F : Type} {state : State F} {n nId owner : Nat} {objects ids : Role → Nat}
    (h : View state n nId owner [.output,.work,.twiddle,.data] objects ids) :
    Locals state variableName variableType (variableId nId ids) owner (variableValue n objects) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    cases v with
    | none=>exact h.nLookup
    | some r=>exact h.lookup r (all_roles r)
  · intro v
    cases v with
    | none=>exact h.nSlot
    | some r=>exact h.slots r (all_roles r)
  · intro v w same
    cases v with
    | none=>
      cases w with
      | none=>rfl
      | some r=>exact False.elim (h.nSeparate r (all_roles r) same)
    | some r=>
      cases w with
      | none=>exact False.elim (h.nSeparate r (all_roles r) same.symm)
      | some s=>exact congrArg some (h.differentSlots r (all_roles r) s (all_roles s) same)
  · rw [←h.scope]
    exact h.well.current

def MemoryReady {F : Type} (state : State F) (n : Nat) (objects : Role → Nat) (done : List Role) (r : Role) : Prop :=
  if r∈done then WordArrayRep state (objects r) (length n r) (fun _=>0)
  else state.objects (objects r)=some (zeroPrefixObject (length n r) 0)

structure InitializedView {F : Type} (state : State F) (n nId owner : Nat)
    (objects ids : Role → Nat) (done : List Role) : Prop where
  locals : Locals state variableName variableType (variableId nId ids) owner (variableValue n objects)
  distinct : Function.Injective objects
  memory : ∀r, MemoryReady state n objects done r
  well : WellScoped state
  host : state.mode=.host
  scope : state.scope=owner

theorem View.initialized {F : Type} {state : State F} {n nId owner : Nat} {objects ids : Role → Nat}
    (h : View state n nId owner [.output,.work,.twiddle,.data] objects ids) :
    InitializedView state n nId owner objects ids [] :=
  ⟨h.locals,fun r s eq=>h.differentObjects r (all_roles r) s (all_roles s) eq,
    fun r=>h.raw r (all_roles r),h.well,h.host,h.scope⟩

theorem raw_ne_slot {F : Type} {state : State F} {object length id owner : Nat}
    {ctype : CType} {value : Value}
    (raw : state.objects object=some (zeroPrefixObject length 0))
    (slot : Slot state id owner ctype value) : object≠id := by
  intro same
  subst id
  have eq:=Option.some.inj (raw.symm.trans slot.object)
  have storage:=congrArg Object.storage eq
  cases storage

/-- An actual raw-buffer zero call preserves every actual main local slot. -/
theorem InitializedView.locals_after_zero {F : Type} {before after : State F}
    {n nId owner : Nat} {objects ids : Role → Nat} {done : List Role} {next : Role}
    (h : InitializedView before n nId owner objects ids done)
    (notDone : next∉done) (frame : ZeroRaw.FullCallerFrame before after (objects next)) :
    Locals after variableName variableType (variableId nId ids) owner (variableValue n objects) := by
  have raw : before.objects (objects next)=some (zeroPrefixObject (length n next) 0) := by
    simpa only [MemoryReady,if_neg notDone] using h.memory next
  refine ⟨?_,?_,h.locals.distinct,?_⟩
  · rw [frame.environment]
    exact h.locals.lookup
  · intro v
    have slot:=h.locals.slots v
    exact ⟨slot.storable,(frame.objects _ (h.well.objectIds _ _ slot.object)
      (Ne.symm (raw_ne_slot raw slot))).trans slot.object⟩
  · exact h.locals.bound.trans_le frame.nextScope

/-- The next source zero_words call changes raw bytes into typed zero words,
while preserving all earlier typed arrays and all later raw allocations. -/
theorem InitializedView.after_zero {F : Type} {before after : State F}
    {n nId owner : Nat} {objects ids : Role → Nat} {done : List Role} {next : Role}
    (h : InitializedView before n nId owner objects ids done) (notDone : next∉done)
    (frame : ZeroRaw.FullCallerFrame before after (objects next))
    (words : WordArrayRep after (objects next) (length n next) (fun _=>0)) :
    InitializedView after n nId owner objects ids (next::done) := by
  refine ⟨h.locals_after_zero notDone frame,h.distinct,?_,frame.well,frame.mode.trans h.host,frame.scope.trans h.scope⟩
  intro r
  by_cases same : r=next
  · subst r
    simpa only [MemoryReady,List.mem_cons_self,if_pos] using words
  · have different : objects r≠objects next:=fun eq=>same (h.distinct eq)
    by_cases completed : r∈done
    · have rep : WordArrayRep before (objects r) (length n r) (fun _=>0) := by
        simpa only [MemoryReady,if_pos completed] using h.memory r
      have rep' : WordArrayRep after (objects r) (length n r) (fun _=>0) :=
        ⟨frame.mode.trans rep.1,(frame.objects _ (h.well.objectIds _ _ rep.2.1) different).trans rep.2.1,rep.2.2⟩
      simpa only [MemoryReady,List.mem_cons,if_pos (Or.inr completed)] using rep'
    · have raw : before.objects (objects r)=some (zeroPrefixObject (length n r) 0) := by
        simpa only [MemoryReady,if_neg completed] using h.memory r
      have raw' := (frame.objects _ (h.well.objectIds _ _ raw) different).trans raw
      have notLater : r∉next::done := by simp [same,completed]
      simpa only [MemoryReady,if_neg notLater] using raw'

#print axioms View.locals
#print axioms InitializedView.locals_after_zero
#print axioms InitializedView.after_zero
end RH080Next.FFTPV.MainAllocation
