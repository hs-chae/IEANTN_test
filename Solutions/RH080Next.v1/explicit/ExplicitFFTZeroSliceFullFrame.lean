/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroCallDeterminism
import ExplicitApplicationBirthFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ZeroSlice
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings PureDeterminism

structure FullCallerFrame {F : Type} (before after : State F) (object : Nat)
    extends CopyLoop.CallerFrame before after object : Prop where
  nextObject : before.nextObject≤after.nextObject
  nextScope : before.nextScope≤after.nextScope
  mode : after.mode=before.mode

theorem FullCallerFrame.birth {F : Type} {before after : State F} {object cutoff : Nat}
    (h : FullCallerFrame before after object) (fresh : cutoff≤before.nextObject) :
    ApplicationBirthFrame.Frame cutoff before after [object] := by
  refine ⟨h.well,fresh.trans h.nextObject,h.nextObject,h.nextScope,h.mode,h.foreign,?_⟩
  intro id old absent
  exact h.objects id (lt_of_lt_of_le old fresh) (by simpa using absent)

/-- The actual arbitrary-slice zero call retains the caller's full bookkeeping.
Every field follows from real parameter/local births, loop and scope exit. -/
theorem zero_words_call_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    (before : State F) (object size start length : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object size old)
    (bound : start+length≤size) (fits : length<2^64) :
    ∃after, Call context "zero_words"
      [.pointer (wordPointer object start),.integer (integer64 length)] before
      (.value (.integer (integer64 0))) after ∧
      WordArrayRep after object size (zeroData old start length) ∧
      FullCallerFrame before after object := by
  let entry : State F := {before.enterScope with environment:=[]}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  obtain ⟨aState,nState,jState,da,dn,dj,view⟩ := initialize_parameters we rfl rep bound fits
  obtain ⟨middle,run,result⟩ := loop_execution context length view (by omega)
  let after : State F := {middle.leaveScope entry.scope before.environment with scope:=before.scope}
  have nscope : nState.scope=entry.scope := (declare_frame dn).1.trans (declare_frame da).1
  have params : bindParameters entry zero_words_ast.parameters
      [.pointer (wordPointer object start),.integer (integer64 length)]=some nState := by
    change bindParameters entry [(.pointer .u64,"a"),(.u64,"n")]
      [.pointer (wordPointer object start),.integer (integer64 length)]=some nState
    simp [bindParameters,da,dn]
  have called : Call context "zero_words"
      [.pointer (wordPointer object start),.integer (integer64 length)] before
      (.value (.integer (integer64 0))) after := by
    apply Call.internal (function:=zero_words_ast) (entered:=nState) (middle:=middle)
      selected ZeroLoop.loop_is_actual params
    · apply Body.finish
      · exact .cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dj)
          (.cons run (.abrupt (.returnSome (.literal (.integer 0 "ULL") _
            (.integer (integer64 0)) (by rfl))) (by intro h; cases h)))
      · intro label h
        cases h
    · exact convert64 0 (by norm_num)
    · simp only [after,nscope]
  obtain ⟨known,original,knownRep,knownFrame⟩ := zero_words_call context selected before
    object size start length old well rep bound fits
  have same := (ZeroCallUnique.returned_call_unique selected original called).2
  cases same
  have chain : Declarations entry jState := .cons da (.cons dn (.cons dj (.nil jState)))
  have fields := chain.fields
  have effect := SourceNoAlloc.exec_effect run
    (by simp [ZeroLoop.loop,ZeroLoop.condition,ZeroLoop.loopBody,ZeroLoop.increment,
      zeroStoreStmt,SourceNoAlloc.Only,SourcePure.CallFree]) view.well
  refine ⟨after,called,knownRep,knownFrame,?_,?_,?_⟩
  · change entry.nextObject≤middle.nextObject
    rw [effect.nextObject]
    exact fields.1
  · have ns := fields.2.2.1
    have mono := effect.nextScope
    change jState.nextScope=before.nextScope+1 at ns
    change before.nextScope≤middle.nextScope
    omega
  · exact effect.mode.trans fields.2.2.2.1

#print axioms FullCallerFrame.birth
#print axioms zero_words_call_framed
end RH080Next.FFTPV.ZeroSlice
