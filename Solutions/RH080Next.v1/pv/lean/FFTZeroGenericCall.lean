/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroParameters
import FFTZeroCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ZeroFrame
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- Application-call frame proved from this source function, never trusted as a
platform success/result assumption. All pre-existing nonbuffer objects survive. -/
structure CallerFrame {F : Type} (before after : State F) (object : Nat) : Prop where
  environment : after.environment=before.environment
  scope : after.scope=before.scope
  foreign : after.foreign=before.foreign
  well : WellScoped after
  objects : ∀id,id<before.nextObject → id≠object → after.objects id=before.objects id

/-- The actual zero_words function in arbitrary caller heaps and scopes.
The input memory consists of the generic calloc bytes, not a trusted typed
application representation. Parameters and local j are proved initialized. -/
theorem zero_words_call {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    (before : State F) (object length : Nat) (well : WellScoped before)
    (host : before.mode=.host)
    (buffer : before.objects object=some (zeroPrefixObject length 0)) (fits : length<2^64) :
    ∃after,Call context "zero_words"
      [.pointer (wordPointer object 0),.integer (integer64 length)] before
      (.value (.integer (integer64 0))) after ∧
      WordArrayRep after object length (fun _=>0) ∧ CallerFrame before after object := by
  let entry : State F := {before.enterScope with environment:=[]}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  obtain ⟨aState,nState,jState,da,dn,dj,view⟩ := initialize_parameters we host rfl buffer fits
  obtain ⟨middle,run,_,words,frame⟩ := loop_zero_output_frame context view
  let after : State F := {middle.leaveScope entry.scope before.environment with scope:=before.scope}
  have nscope : nState.scope=entry.scope :=
    (declare_frame dn).1.trans (declare_frame da).1
  have params : bindParameters entry zero_words_ast.parameters
      [.pointer (wordPointer object 0),.integer (integer64 length)]=some nState := by
    change bindParameters entry [(.pointer .u64,"a"),(.u64,"n")]
      [.pointer (wordPointer object 0),.integer (integer64 length)]=some nState
    simp [bindParameters,da,dn]

  have called : Call context "zero_words"
      [.pointer (wordPointer object 0),.integer (integer64 length)] before
      (.value (.integer (integer64 0))) after := by
    apply Call.internal (function:=zero_words_ast) (entered:=nState) (middle:=middle)
      selected ZeroLoop.loop_is_actual params
    · apply Body.finish
      · exact .cons (.declareSome
          (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dj)
          (.cons run (.abrupt (.returnSome (.literal (.integer 0 "ULL") _
            (.integer (integer64 0)) (by rfl))) (by intro he; cases he)))
      · intro label he
        cases he
    · exact convert64 0 (by norm_num)
    · simp only [after,nscope]
  have chain : Declarations entry jState :=
    .cons da (.cons dn (.cons dj (.nil jState)))
  have fields:=chain.fields
  have effect:=SourceNoAlloc.exec_effect run
    (by simp [ZeroLoop.loop,ZeroLoop.condition,ZeroLoop.loopBody,ZeroLoop.increment,
      zeroStoreStmt,SourceNoAlloc.Only,SourcePure.CallFree]) view.well
  have oldObjects : ∀id,id<before.nextObject → id≠object → after.objects id=before.objects id := by
    intro id old different
    have untouched : id∉[parameterIds entry.nextObject Var.j,object] := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
      exact ⟨by simp only [parameterIds]; change id≠before.nextObject+2; omega,different⟩
    have same : middle.objects id=before.objects id :=
      (frame.outside id untouched).trans (fields.2.2.2.2 id old)
    change (middle.objects id).map _=before.objects id
    rw [same]
    cases present : before.objects id with
    | none => rfl
    | some obj =>
      have storage : obj.storage≠.automatic entry.scope := by
        intro bad
        have bound:=well.automatic id obj before.nextScope present bad
        omega
      simp [storage]
  have afterWell : WellScoped after := by
    apply wellScoped_scope (wellScoped_leave effect.well entry.scope before.environment)
    change before.scope<middle.nextScope
    have b:=well.current
    have nss:=fields.2.2.1
    have nsf:=frame.nextScope
    change jState.nextScope=before.nextScope+1 at nss
    omega
  have afterWords : WordArrayRep after object length (fun _=>0) := by
    refine ⟨words.1,?_,words.2.2⟩
    change (middle.objects object).map _=some (wordObject length (fun _=>0))
    rw [words.2.1]
    simp [wordObject]
  refine ⟨after,called,afterWords,rfl,rfl,?_,afterWell,oldObjects⟩
  have fa : aState.foreign=entry.foreign := declare_foreign da
  have fn : nState.foreign=aState.foreign := declare_foreign dn
  have fj : jState.foreign=nState.foreign := declare_foreign dj
  have result : middle.foreign=entry.foreign := effect.foreign.trans (fj.trans (fn.trans fa))
  exact result

/-- Source syntax, the source's actual parameter/local construction, full loop
execution and final typed memory are all consumed in this general helper fact.
It is not a statement about execution or numerical output of the whole FFT. -/
theorem source_zero_words_call (before : State Unit) (object length : Nat)
    (well : WellScoped before) (host : before.mode=.host)
    (buffer : before.objects object=some (zeroPrefixObject length 0)) (fits : length<2^64) :
    GoldbachDirect.Correspondence.SourceSyntaxCorresponds FFTPV.source FFTPV.program ∧
    ∃after,Call ZeroLoop.sourceContext "zero_words"
      [.pointer (wordPointer object 0),.integer (integer64 length)] before
      (.value (.integer (integer64 0))) after ∧
      WordArrayRep after object length (fun _=>0) ∧ CallerFrame before after object :=
  ⟨actual_source_syntax,zero_words_call ZeroLoop.sourceContext (by rfl)
    before object length well host buffer fits⟩

#print axioms zero_words_call
#print axioms source_zero_words_call
end RH080Next.FFTPV.ZeroFrame
