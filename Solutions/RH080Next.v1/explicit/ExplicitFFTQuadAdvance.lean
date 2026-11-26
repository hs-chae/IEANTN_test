/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadAdd
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

theorem View.advance_execution {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo bo j cutoff : Nat}
    {ids : InputLoader.Var → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : View before input workObject fo bo 2 j cutoff ids auxIds (absoluteValues input j) dataMemory workData true) :
    ∃after,Exec context before advanceStatement .normal after ∧ Every context before advanceStatement .normal after ∧
      LoopView after input workObject fo (j+1) (fun p=> ids (.inl p)) auxIds dataMemory workData ∧
      ApplicationBirthFrame.Frame cutoff before after [workObject,ids (.inl .j)] ∧
      after.environment=before.environment ∧ after.scope=before.scope:=by
  have shape:=input.profile.shape
  have j64 : j<2^64:=by have a:=h.body.active;omega
  have next64 : j+1<2^64:=by have a:=h.body.active;omega
  have evaluated : Eval context before (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL")))) (.integer (integer64 (j+1))) before:=
    .paren (.binaryLR (h.body.parameter_eval context .j) (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
      (by simp only [parameterValues,binary,binary64_add _ _ j64 (show 1<2^64 by norm_num) next64,Option.map_some]))
  obtain ⟨after,run,every,post,stored,frame⟩:=h.body.bindings.assign context h.body.well (.inl .j) (by trivial) (.integer (integer64 (j+1)))
    (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL")))) (ZeroFrame.u64_storable _ next64) evaluated (by trivial)
    [workObject,ids (.inl .j)] h.body.fresh (Or.inl (by simp))
  have array:=ProductInner.array_store_old h.body.array (h.body.separate (.inl .j) (by trivial)) stored
  have work:=ProductInner.array_store_old h.work (h.workSeparate (.inl .j) (by trivial)) stored
  have aux:=ApplicationBirthFrame.locals_store_other h.aux (fun a=>(h.cross .j a).symm) stored
  have parameters : Locals after parameterName parameterType (fun p=> ids (.inl p)) fo (parameterValues input (j+1)):=by
    constructor
    · intro p;cases p with
      | data=> exact post.lookup (.inl .data) (by trivial)
      | n=> exact post.lookup (.inl .n) (by trivial)
      | j=> exact post.lookup (.inl .j) (by trivial)
    · intro p;cases p with
      | data=> simpa [varType,parameterType,owner,absoluteValues,plannedValues,parameterValues] using post.slots (.inl .data) (by trivial)
      | n=> simpa [varType,parameterType,owner,absoluteValues,plannedValues,parameterValues] using post.slots (.inl .n) (by trivial)
      | j=> simpa [varType,parameterType,owner,absoluteValues,plannedValues,parameterValues] using post.slots (.inl .j) (by trivial)
    · intro a b equal;exact Sum.inl.inj (post.distinct (.inl a) (.inl b) (by trivial) (by trivial) equal)
    · exact post.bound (.inl .data) (by trivial)
  have fields:=SourceLocals.store_frame stored
  have view : LoopView after input workObject fo (j+1) (fun p=> ids (.inl p)) auxIds dataMemory workData:=
    ⟨parameters,aux,array,work,h.different,(fun p=> h.body.separate (.inl p) (by trivial)),
      (fun p=> h.workSeparate (.inl p) (by trivial)),h.auxSeparate,h.cross,(by have a:=h.body.active;omega),h.quadDigits,
      (by simpa only [Bool.true_eq_false,↓reduceIte,partialQuad_succ] using h.quadValue),frame.well⟩
  exact ⟨after,run,every,view,frame,fields.1,fields.2.2.1⟩

#print axioms View.advance_execution
end RH080Next.FFTPV.QuadSource
