/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootRuntimeCalls
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect SourceLocals
open ApplicationBirthFrame

theorem lower_frame {F : Type} {before after : State F} {old cutoff : Nat} {writes : List Nat}
    (h : Frame old before after writes) (lower : cutoff≤old) : Frame cutoff before after writes :=
  ⟨h.well,lower.trans h.fresh,h.nextObject,h.nextScope,h.mode,h.foreign,
    fun id bound outside=>h.outside id (lt_of_lt_of_le bound lower) outside⟩

theorem unary_frame {F : Type} {before after : State F} {object : Nat}
    (h : IncrementSource.FullCallerFrame before after object) : Frame before.nextObject before after [object]:=
  ⟨h.well,h.nextObject,h.nextObject,h.nextScope,h.mode,h.foreign,
    fun id bound outside=>h.objects id bound (by simpa only [List.mem_singleton] using outside)⟩

theorem multiply_frame {F : Type} {before after : State F} {object : Nat}
    (h : MultiplyCall.CallerFrame before after [object,object]) : Frame before.nextObject before after [object] :=
  ⟨h.frame.well,h.frame.fresh,h.frame.nextObject,h.frame.nextScope,h.frame.mode,h.frame.foreign,
    fun id bound outside=>h.frame.outside id bound (by simpa using outside)⟩

theorem full_caller_frame {F : Type} {before after : State F} {object : Nat}
    (environment : after.environment=before.environment) (scope : after.scope=before.scope)
    (h : Frame before.nextObject before after [object]) : IncrementSource.FullCallerFrame before after object :=
  ⟨⟨environment,scope,h.foreign,h.well,fun id bound different=>h.outside id bound (by simpa only [List.mem_singleton] using different)⟩,
    h.nextObject,h.nextScope,h.mode⟩

theorem full_caller_trans {F : Type} {before middle after : State F} {object : Nat}
    (first : IncrementSource.FullCallerFrame before middle object)
    (second : IncrementSource.FullCallerFrame middle after object) : IncrementSource.FullCallerFrame before after object := by
  apply full_caller_frame (second.environment.trans first.environment) (second.scope.trans first.scope)
  exact (unary_frame first).trans (lower_frame (unary_frame second) first.nextObject)

#print axioms full_caller_trans
end RH080Next.FFTPV.RootSource
