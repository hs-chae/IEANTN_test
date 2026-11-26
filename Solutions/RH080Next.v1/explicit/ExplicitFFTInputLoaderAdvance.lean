/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderMirror
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def advanceStatement : Stmt:=.assign (.variable "j") (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL"))))

theorem source_advance : (ProductRow.items loopBody)[13]?=some advanceStatement:=rfl

theorem BodyView.advance_execution {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo j cutoff : Nat}
    {ids : Var → Nat} {memory : Nat → Nat}
    (h : BodyView before input fo bo 5 j cutoff ids (dividedValues input j) memory) :
    ∃after,Exec context before advanceStatement .normal after ∧ Every context before advanceStatement .normal after ∧
      WordArrayRep after input.object (12*input.profile.grid) memory ∧
      Locals after parameterName parameterType (fun p=> ids (.inl p)) fo (parameterValues input (j+1)) ∧
      ApplicationBirthFrame.Frame cutoff before after [input.object,ids (.inl .j)] ∧
      after.environment=before.environment ∧ after.scope=before.scope:=by
  have shape:=input.profile.shape
  have j64 : j<2^64:=by have a:=h.active;omega
  have next64 : j+1<2^64:=by have a:=h.active;omega
  have evaluated : Eval context before (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL")))) (.integer (integer64 (j+1))) before:=
    .paren (.binaryLR (h.parameter_eval context .j) (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
      (by simp only [parameterValues,binary,binary64_add _ _ j64 (show 1<2^64 by norm_num) next64,Option.map_some]))
  obtain ⟨after,run,every,post,stored,frame⟩:=h.bindings.assign context h.well (.inl .j) (by trivial) (.integer (integer64 (j+1)))
    (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL")))) (ZeroFrame.u64_storable _ next64) evaluated (by trivial)
    [input.object,ids (.inl .j)] h.fresh (Or.inl (by simp))
  have array:=ProductInner.array_store_old h.array (h.separate (.inl .j) (by trivial)) stored
  have locals : Locals after parameterName parameterType (fun p=> ids (.inl p)) fo (parameterValues input (j+1)):=by
    constructor
    · intro p
      cases p with
      | data=> exact post.lookup (.inl .data) (by trivial)
      | n=> exact post.lookup (.inl .n) (by trivial)
      | j=> exact post.lookup (.inl .j) (by trivial)
    · intro p
      cases p with
      | data=> simpa [varType,parameterType,owner,dividedValues,branchValues,plannedValues,parameterValues] using post.slots (.inl .data) (by trivial)
      | n=> simpa [varType,parameterType,owner,dividedValues,branchValues,plannedValues,parameterValues] using post.slots (.inl .n) (by trivial)
      | j=> simpa [varType,parameterType,owner,dividedValues,branchValues,plannedValues,parameterValues] using post.slots (.inl .j) (by trivial)
    · intro a b equal
      exact Sum.inl.inj (post.distinct (.inl a) (.inl b) (by trivial) (by trivial) equal)
    · exact post.bound (.inl .data) (by trivial)
  have fields:=SourceLocals.store_frame stored
  exact ⟨after,run,every,array,locals,frame,fields.1,fields.2.2.1⟩

#print axioms BodyView.advance_execution
end RH080Next.FFTPV.InputLoader
