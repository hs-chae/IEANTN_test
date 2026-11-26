/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLeafContract
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

private theorem chain_foreign {F : Type} {before after : State F} (h : Declarations before after) :
    after.foreign=before.foreign := by
  induction h with
  | nil => rfl
  | cons declared tail ih => exact ih.trans (declare_foreign declared)

/-- The real function entry binds all nine arguments and supplies the source
header view, with no preinitialized local or successful-allocation premise. -/
theorem recursive_entry {F : Type} {caller : State F} {total : Nat} {buffers : Buffers total}
    {start index step n : Nat} {input table output work : Nat → Nat}
    (shape : IndexShape start index step n total) (well : WellScoped caller)
    (arrays : ∀r,WordArrayRep caller (buffers.object r) (buffers.length r) (bufferData input table output work r)) :
    ∃entered parameterIds,
      bindParameters {caller.enterScope with environment:=[]} FFTRecursivePV.fft_recursive_ast.parameters
        (arguments (buffers.object .output) (buffers.object .input) (buffers.object .twiddle)
          (buffers.object .work) start index step n total)=some entered ∧
      Header.View entered buffers start index step n 0 parameterIds caller.nextScope input table output work ∧
      Frame caller.nextObject caller.enterScope entered [buffers.object .output,buffers.object .work] ∧
      entered.scope=caller.nextScope := by
  let entry : State F := {caller.enterScope with environment:=[]}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  have scalarBounds:=shape.scalar_bounds
  obtain ⟨entered,bound,params,chain,pwell,pno,pscope,pns⟩:=initialize_parameters
    (buffers.object .output) (buffers.object .input) (buffers.object .twiddle) (buffers.object .work)
    start index step n total we rfl scalarBounds.1 scalarBounds.2.1 scalarBounds.2.2.1
      scalarBounds.2.2.2.1 scalarBounds.2.2.2.2
  have fields:=chain.fields
  have arraysP : ∀r,WordArrayRep entered (buffers.object r) (buffers.length r) (bufferData input table output work r) := by
    intro r
    have old:=well.objectIds _ _ (arrays r).2.1
    exact ⟨fields.2.2.2.1.trans (arrays r).1,
      (fields.2.2.2.2 _ old).trans (arrays r).2.1,(arrays r).2.2⟩
  have pframe : Frame caller.nextObject caller.enterScope entered [buffers.object .output,buffers.object .work] := by
    refine ⟨pwell,fields.1,fields.1,?_,fields.2.2.2.1,(chain_foreign chain).trans (show entry.foreign=caller.enterScope.foreign from rfl),?_⟩
    · rw [pns]
    · intro id old absent;exact fields.2.2.2.2 id old
  exact ⟨entered,_,bound,Header.View.initial params arraysP pwell pscope,pframe,pscope⟩

/-- A fresh function-owned local cannot be a preexisting caller object, even
when recursive calls and block births have advanced both allocation clocks. -/
theorem fresh_function_slot {F : Type} {caller current : State F} {id : Nat} {ctype : CType} {value : Value}
    {writes : List Nat} (well : WellScoped caller)
    (frame : Frame caller.nextObject caller.enterScope current writes)
    (slot : Slot current id caller.nextScope ctype value) (outside : id∉writes) : caller.nextObject ≤ id := by
  by_contra notFresh
  have old : id<caller.nextObject := by omega
  have original : caller.objects id=some (scalarObject caller.nextScope value.byteSize value) :=
    (frame.outside id old outside).symm.trans slot.object
  have impossible:=well.automatic id _ caller.nextScope original (by rfl)
  omega

#print axioms recursive_entry
#print axioms fresh_function_slot
end RH080Next.FFTPV.RecursiveSource
