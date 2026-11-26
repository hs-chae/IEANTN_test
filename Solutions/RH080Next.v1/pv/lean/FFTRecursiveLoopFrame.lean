/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveBindingsFrame
import FFTRecursiveBufferMap
import FFTComplexFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect WordArrays SourceLocals SourceScalarSlots SourceBindings ProductInner

/-- Generic local preservation uses actual automatic storage and the real
source helper's caller frame, including scope and lifetime metadata. -/
theorem locals_after_array_call {F I : Type} {before after : State F}
    {names : I → String} {types : I → CType} {ids : I → Nat} {owner : Nat} {values : I → Value}
    {writes : List Nat} {total : Nat} {buffers : Buffers total}
    {input table output work : Nat → Nat}
    (well : WellScoped before) (params : Locals before names types ids owner values)
    (arrays : ∀r,WordArrayRep before (buffers.object r) (buffers.length r) (bufferData input table output work r))
    (frame : MultiplyCall.CallerFrame before after writes)
    (writesBuffers : ∀object ∈ writes,∃r,object=buffers.object r) :
    Locals after names types ids owner values := by
  refine ⟨?_,?_,params.distinct,params.bound.trans_le frame.frame.nextScope⟩
  · rw [frame.environment];exact params.lookup
  · intro v
    apply ComplexSource.slot_after_call well (params.slots v) frame
    intro member
    obtain ⟨r,same⟩ := writesBuffers (ids v) member
    exact (array_ne_slot (arrays r) (params.slots v)) same.symm

/-- A source helper can update output/work while the actual input, global
Twiddle table and all typed loop variables are preserved by its proven frame. -/
theorem LoopView.after_array_call {F : Type} {before after : State F}
    {total : Nat} {buffers : Buffers total} {start index step n owner j : Nat}
    {ids : LoopVar → Nat} {input table output work newOutput newWork : Nat → Nat} {writes : List Nat}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (frame : MultiplyCall.CallerFrame before after writes)
    (writesBuffers : ∀object ∈ writes,∃r,object=buffers.object r)
    (inputOutside : buffers.object .input ∉ writes) (tableOutside : buffers.object .twiddle ∉ writes)
    (outputAfter : WordArrayRep after (buffers.object .output) (buffers.length .output) newOutput)
    (workAfter : WordArrayRep after (buffers.object .work) (buffers.length .work) newWork) :
    LoopView after buffers start index step n ids owner j input table newOutput newWork := by
  refine ⟨?_,?_,frame.frame.well,h.active⟩
  · apply bindings_after_call h.bindings h.well frame
    intro v member
    obtain ⟨r,same⟩ := writesBuffers (ids v) member
    exact (array_ne_slot (h.arrays r) (h.bindings.slots v)) same.symm
  · intro r
    cases r
    · exact outputAfter
    · exact ComplexSource.word_array_after_call h.well (h.arrays .input) frame inputOutside
    · exact ComplexSource.word_array_after_call h.well (h.arrays .twiddle) frame tableOutside
    · exact workAfter

#print axioms LoopView.after_array_call
end RH080Next.FFTPV.RecursiveSource
