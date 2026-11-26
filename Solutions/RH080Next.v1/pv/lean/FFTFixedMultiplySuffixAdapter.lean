/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyBegin
import FFTFixedMultiplySuffixSign
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyParameters
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- Actual automatic pointer and integer slots cannot be the same object.
This follows from their concrete stored values, not a guessed allocator ID. -/
theorem pointer_integer_slots_different {F : Type} {state : State F} {pointerId integerId pOwner iOwner : Nat}
    {pointer : Pointer} {n : Nat}
    (p : Slot state pointerId pOwner (.pointer .u64) (.pointer pointer))
    (i : Slot state integerId iOwner .u64 (.integer (integer64 n))) : pointerId≠integerId := by
  intro equal
  have po:=p.object
  rw [equal] at po
  have objectEq:=Option.some.inj (po.symm.trans i.object)
  have cells:=congrArg (fun object : Object=>object.cells 0) objectEq
  simp [scalarObject] at cells

/-- The actual typed host allocation cannot alias an automatic scalar slot. -/
theorem array_slot_different {F : Type} {state : State F} {object size id owner : Nat}
    {data : Nat→Nat} {ctype : CType} {value : Value}
    (rep : WordArrayRep state object size data) (slot : Slot state id owner ctype value) : object≠id:=by
  intro equal
  have present:=rep.2.1
  rw [equal] at present
  have objects:=Option.some.inj (present.symm.trans slot.object)
  have storage:=congrArg Object.storage objects
  cases storage

def suffixIds (parameterIds : Var→Nat) (iId : Nat) : MultiplySuffix.PVar→Nat
  | .out=>parameterIds .output | .a=>parameterIds .a | .b=>parameterIds .b | .work=>parameterIds .work | .i=>iId

/-- Real post-core bindings are extended to exactly the five source names
consumed by the actual suffix, preserving the original function owners. -/
theorem suffix_bindings {F : Type} {state : State F}
    {outObj outStart aObj aSize aStart bObj bSize bStart workObj workSize workStart owner iId : Nat}
    {parameterIds : Var→Nat} {a b data : Nat→Nat}
    (params : Locals state name type parameterIds owner
      (value outObj outStart aObj aStart bObj bStart workObj workStart))
    (core : ProductOuter.View state aObj aSize aStart bObj bSize bStart workObj workSize workStart
      (coreIds parameterIds iId) (fun _=>owner) a b data 5) :
    ProductInner.Bindings state MultiplySuffix.pName MultiplySuffix.pType
      (suffixIds parameterIds iId) (fun _=>owner)
      (MultiplySuffix.pValue outObj outStart aObj aStart bObj bStart workObj workStart 5) := by
  have different : ∀v,parameterIds v≠iId:=by
    intro v
    cases v
    · exact pointer_integer_slots_different (params.slots Var.output) (core.locals.slots ProductOuter.PVar.i)
    · exact pointer_integer_slots_different (params.slots Var.a) (core.locals.slots ProductOuter.PVar.i)
    · exact pointer_integer_slots_different (params.slots Var.b) (core.locals.slots ProductOuter.PVar.i)
    · exact pointer_integer_slots_different (params.slots Var.work) (core.locals.slots ProductOuter.PVar.i)
  refine ⟨?_,?_,?_,?_⟩
  · intro v;cases v
    · exact params.lookup Var.output
    · exact params.lookup Var.a
    · exact params.lookup Var.b
    · exact params.lookup Var.work
    · exact core.locals.lookup ProductOuter.PVar.i
  · intro v;cases v
    · exact params.slots Var.output
    · exact params.slots Var.a
    · exact params.slots Var.b
    · exact params.slots Var.work
    · exact core.locals.slots ProductOuter.PVar.i
  · intro u v equal
    cases u <;> cases v
    · rfl
    · change parameterIds Var.output=parameterIds Var.a at equal
      exact False.elim ((by decide : Var.output≠Var.a) (params.distinct equal))
    · change parameterIds Var.output=parameterIds Var.b at equal
      exact False.elim ((by decide : Var.output≠Var.b) (params.distinct equal))
    · change parameterIds Var.output=parameterIds Var.work at equal
      exact False.elim ((by decide : Var.output≠Var.work) (params.distinct equal))
    · change parameterIds Var.output=iId at equal
      exact False.elim (different Var.output equal)
    · change parameterIds Var.a=parameterIds Var.output at equal
      exact False.elim ((by decide : Var.a≠Var.output) (params.distinct equal))
    · rfl
    · change parameterIds Var.a=parameterIds Var.b at equal
      exact False.elim ((by decide : Var.a≠Var.b) (params.distinct equal))
    · change parameterIds Var.a=parameterIds Var.work at equal
      exact False.elim ((by decide : Var.a≠Var.work) (params.distinct equal))
    · change parameterIds Var.a=iId at equal
      exact False.elim (different Var.a equal)
    · change parameterIds Var.b=parameterIds Var.output at equal
      exact False.elim ((by decide : Var.b≠Var.output) (params.distinct equal))
    · change parameterIds Var.b=parameterIds Var.a at equal
      exact False.elim ((by decide : Var.b≠Var.a) (params.distinct equal))
    · rfl
    · change parameterIds Var.b=parameterIds Var.work at equal
      exact False.elim ((by decide : Var.b≠Var.work) (params.distinct equal))
    · change parameterIds Var.b=iId at equal
      exact False.elim (different Var.b equal)
    · change parameterIds Var.work=parameterIds Var.output at equal
      exact False.elim ((by decide : Var.work≠Var.output) (params.distinct equal))
    · change parameterIds Var.work=parameterIds Var.a at equal
      exact False.elim ((by decide : Var.work≠Var.a) (params.distinct equal))
    · change parameterIds Var.work=parameterIds Var.b at equal
      exact False.elim ((by decide : Var.work≠Var.b) (params.distinct equal))
    · rfl
    · change parameterIds Var.work=iId at equal
      exact False.elim (different Var.work equal)
    · change iId=parameterIds Var.output at equal
      exact False.elim (different Var.output equal.symm)
    · change iId=parameterIds Var.a at equal
      exact False.elim (different Var.a equal.symm)
    · change iId=parameterIds Var.b at equal
      exact False.elim (different Var.b equal.symm)
    · change iId=parameterIds Var.work at equal
      exact False.elim (different Var.work equal.symm)
    · rfl
  · intro v;exact params.bound

/-- The current output allocation exists after the core even if output and
scratch share one allocation. No output bytes or successful effects are assumed. -/
theorem current_output_rep {F : Type} {before after : State F}
    {outObj outSize workObj workSize : Nat} {old data : Nat→Nat}
    (well : WellScoped before) (outRep : WordArrayRep before outObj outSize old)
    (workRep : WordArrayRep after workObj workSize data)
    (shape : outObj=workObj → outSize=workSize)
    (frame : ∀id,id<before.nextObject → id≠workObj → after.objects id=before.objects id) :
    ∃current,WordArrayRep after outObj outSize current:=by
  by_cases same : outObj=workObj
  · have sizes:=shape same
    subst outObj;subst outSize
    exact ⟨data,workRep⟩
  · have oldId:=well.objectIds _ _ outRep.2.1
    exact ⟨old,⟨workRep.1,(frame outObj oldId same).trans outRep.2.1,outRep.2.2⟩⟩

#print axioms pointer_integer_slots_different
#print axioms array_slot_different
#print axioms suffix_bindings
#print axioms current_output_rep
end RH080Next.FFTPV.MultiplyParameters
