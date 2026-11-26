/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexArguments
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

/-- Actual automatic pointer/status slots outside the helper's actual write
objects survive its real Call; births and scope clocks are accounted for. -/
theorem slot_after_call {F : Type} {before after : State F} {writes : List Nat}
    {id owner : Nat} {type : CType} {value : Value}
    (well : WellScoped before) (slot : Slot before id owner type value)
    (frame : MultiplyCall.CallerFrame before after writes) (outside : id∉writes) :
    Slot after id owner type value:=
  ⟨slot.storable,(frame.frame.outside id (well.objectIds _ _ slot.object) outside).trans slot.object⟩

theorem locals_after_call {F : Type} {before after : State F} {writes : List Nat}
    {ids : PVar→Nat} {owner : Nat} {values : PVar→Value}
    (well : WellScoped before) (params : Locals before pName pType ids owner values)
    (frame : MultiplyCall.CallerFrame before after writes) (outside : ∀r,ids r∉writes) :
    Locals after pName pType ids owner values:=by
  refine ⟨?_,fun r=>slot_after_call well (params.slots r) frame (outside r),params.distinct,?_⟩
  · rw [frame.environment]
    exact params.lookup
  · exact params.bound.trans_le frame.frame.nextScope

theorem word_array_after_call {F : Type} {before after : State F} {writes : List Nat}
    {object size : Nat} {data : Nat→Nat}
    (well : WellScoped before) (rep : WordArrayRep before object size data)
    (frame : MultiplyCall.CallerFrame before after writes) (outside : object∉writes) :
    WordArrayRep after object size data:=
  ⟨frame.frame.mode.trans rep.1,(frame.frame.outside object (well.objectIds _ _ rep.2.1) outside).trans rep.2.1,rep.2.2⟩

/-- A single output-object caller frame is converted without any extra
application or allocator assumption. -/
theorem add_caller_frame {F : Type} {before after : State F} {object : Nat}
    (frame : IncrementSource.FullCallerFrame before after object) :
    MultiplyCall.CallerFrame before after [object]:=by
  refine ⟨frame.environment,frame.scope,frame.well,frame.nextObject,frame.nextObject,frame.nextScope,
    frame.mode,frame.foreign,?_⟩
  intro id old outside
  exact frame.objects id old (by simpa only [List.mem_singleton] using outside)

#print axioms slot_after_call
#print axioms locals_after_call
#print axioms word_array_after_call
#print axioms add_caller_frame
end RH080Next.FFTPV.ComplexSource
