/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadPrefix
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

theorem unary_caller {F : Type} {before after : State F} {object : Nat}
    (frame : IncrementSource.FullCallerFrame before after object) : MultiplyCall.CallerFrame before after [object]:=
  ⟨frame.environment,frame.scope,unary_frame frame⟩

theorem small_caller {F : Type} {before after : State F} {object : Nat}
    (frame : MultiplySmallSource.FullCallerFrame before after object) : MultiplyCall.CallerFrame before after [object]:=
  ⟨frame.environment,frame.scope,frame.well,frame.nextObject,frame.nextObject,frame.nextScope,frame.mode,frame.foreign,
    fun id bound outside=>frame.objects id bound (by simpa only [List.mem_singleton] using outside)⟩

theorem View.after_work_call {F : Type} {before after : State F} {input : InputLoader.Input} {workObject fo bo count j cutoff : Nat}
    {ids : InputLoader.Var → Nat} {auxIds : Aux → Nat} {values : InputLoader.Var → Value} {dataMemory old workData : Nat → Nat} {pending nextPending : Bool}
    (h : View before input workObject fo bo count j cutoff ids auxIds values dataMemory old pending)
    (frame : MultiplyCall.CallerFrame before after [workObject])
    (array : WordArrayRep after workObject 512 workData) (digits : ∀k<6,workData (208+k)<base)
    (value : FFT.Limbs.magnitude base 6 (fun k=>workData (208+k))=partialQuad input.profile j+(if nextPending then term input.profile j else 0)) :
    View after input workObject fo bo count j cutoff ids auxIds values dataMemory workData nextPending:=by
  have body : BodyView after input fo bo count j cutoff ids values dataMemory:=
    ⟨ComplexSource.word_array_after_call h.body.well h.body.array frame (by simpa using h.different),
      h.body.bindings.after_call h.body.well frame (by intro v hv;simpa using (h.workSeparate v hv).symm),
      h.body.parameters,h.body.separate,frame.frame.well,frame.scope.trans h.body.scope,h.body.active,h.body.fresh.trans frame.frame.nextObject,h.body.born⟩
  exact ⟨body,generic_locals_after_call h.body.well h.aux frame (by intro v;simpa using (h.auxSeparate v).symm),array,h.different,h.workSeparate,h.auxSeparate,h.auxOld,h.cross,digits,value⟩

theorem Profile.magnitude_selected {F : Type} (p : Profile) (context : Context F) (pinned : context.program=p.program) :
    findFunction context.program "magnitude_into"=some FFTRecursivePV.magnitude_into_ast:=by rw [pinned];cases p <;> rfl

theorem Profile.zero_selected {F : Type} (p : Profile) (context : Context F) (pinned : context.program=p.program) :
    findFunction context.program "zero_words"=some FFTRecursivePV.zero_words_ast:=by rw [pinned];cases p <;> rfl

theorem Profile.multiply_small_selected {F : Type} (p : Profile) (context : Context F) (pinned : context.program=p.program) :
    findFunction context.program "multiply_small"=some FFTRecursivePV.multiply_small_ast:=by rw [pinned];cases p <;> rfl

theorem Profile.add_magnitude_selected {F : Type} (p : Profile) (context : Context F) (pinned : context.program=p.program) :
    findFunction context.program "add_magnitude"=some FFTRecursivePV.add_magnitude_ast:=by rw [pinned];cases p <;> rfl

#print axioms View.after_work_call
end RH080Next.FFTPV.QuadSource
