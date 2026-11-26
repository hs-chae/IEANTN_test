/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroGenericCall
import FFTZeroCallDeterminism
import ExplicitApplicationBirthFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ZeroRaw
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

structure FullCallerFrame {F : Type} (before after : State F) (object : Nat)
    extends ZeroFrame.CallerFrame before after object : Prop where
  nextObject : before.nextObject≤after.nextObject
  nextScope : before.nextScope≤after.nextScope
  mode : after.mode=before.mode

theorem FullCallerFrame.birth {F : Type} {before after : State F} {object cutoff : Nat}
    (h : FullCallerFrame before after object) (fresh : cutoff≤before.nextObject) :
    Frame cutoff before after [object] :=
  ⟨h.well,fresh.trans h.nextObject,h.nextObject,h.nextScope,h.mode,h.foreign,
    fun id old absent=>h.objects id (old.trans_le fresh) (by simpa using absent)⟩

/-- Full clocks and actual caller restoration for the byte-zero birth case.
The actual zero_words loop establishes typed words rather than assuming them. -/
theorem zero_words_call_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    (before : State F) (object length : Nat) (well : WellScoped before) (host : before.mode=.host)
    (raw : before.objects object=some (zeroPrefixObject length 0)) (fits : length<2^64) :
    ∃after,Call context "zero_words" [.pointer (wordPointer object 0),.integer (integer64 length)]
      before (.value (.integer (integer64 0))) after ∧
      WordArrayRep after object length (fun _=>0) ∧ FullCallerFrame before after object := by
  let entry : State F:={before.enterScope with environment:=[]}
  have we : WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  obtain ⟨aState,nState,jState,da,dn,dj,view⟩:=ZeroFrame.initialize_parameters we host rfl raw fits
  obtain ⟨middle,run,_,words,frame⟩:=ZeroFrame.loop_zero_output_frame context view
  let after : State F:={middle.leaveScope entry.scope before.environment with scope:=before.scope}
  have nscope : nState.scope=entry.scope:=(declare_frame dn).1.trans (declare_frame da).1
  have params : bindParameters entry zero_words_ast.parameters
      [.pointer (wordPointer object 0),.integer (integer64 length)]=some nState := by
    change bindParameters entry [(.pointer .u64,"a"),(.u64,"n")]
      [.pointer (wordPointer object 0),.integer (integer64 length)]=some nState
    simp [bindParameters,da,dn]
  have called : Call context "zero_words" [.pointer (wordPointer object 0),.integer (integer64 length)]
      before (.value (.integer (integer64 0))) after := by
    apply Call.internal (function:=zero_words_ast) (entered:=nState) (middle:=middle)
      selected ZeroLoop.loop_is_actual params
    · apply Body.finish
      · exact .cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dj)
          (.cons run (.abrupt (.returnSome (.literal (.integer 0 "ULL") _
            (.integer (integer64 0)) (by rfl))) (by intro bad;cases bad)))
      · intro label bad;cases bad
    · exact convert64 0 (by norm_num)
    · simp only [after,nscope]
  obtain ⟨known,original,knownRep,knownFrame⟩:=ZeroFrame.zero_words_call context selected before object length well host raw fits
  have same:=(ZeroCallUnique.returned_call_unique selected original called).2
  cases same
  have chain : Declarations entry jState:=.cons da (.cons dn (.cons dj (.nil jState)))
  have fields:=chain.fields
  have effect:=SourceNoAlloc.exec_effect run
    (by simp [ZeroLoop.loop,ZeroLoop.condition,ZeroLoop.loopBody,ZeroLoop.increment,
      zeroStoreStmt,SourceNoAlloc.Only,SourcePure.CallFree]) view.well
  refine ⟨after,called,knownRep,knownFrame,?_,?_,?_⟩
  · change entry.nextObject≤middle.nextObject
    rw [effect.nextObject]
    exact fields.1
  · have ns:=fields.2.2.1
    have mono:=effect.nextScope
    change jState.nextScope=before.nextScope+1 at ns
    change before.nextScope≤middle.nextScope
    omega
  · exact effect.mode.trans fields.2.2.2.1

#print axioms zero_words_call_framed
end RH080Next.FFTPV.ZeroRaw
