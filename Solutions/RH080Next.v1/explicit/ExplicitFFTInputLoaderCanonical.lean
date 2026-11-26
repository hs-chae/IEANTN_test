/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderRawStores
import FFTCanonicalFullFrame
import FFTCanonicalDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

theorem BodyView.reframe {F : Type} {before after : State F} {input : Input} {fo bo count j cutoff : Nat}
    {ids : Var → Nat} {values : Var → Value} {old memory : Nat → Nat}
    (h : BodyView before input fo bo count j cutoff ids values old)
    (array : WordArrayRep after input.object (12*input.profile.grid) memory)
    (env : after.environment=before.environment) (scope : after.scope=before.scope) (well : WellScoped after)
    (nextObject : before.nextObject≤ after.nextObject) (nextScope : before.nextScope≤ after.nextScope)
    (objects : ∀id,id< before.nextObject → id≠input.object → after.objects id=before.objects id) :
    BodyView after input fo bo count j cutoff ids values memory:=by
  have bindings : PartialBindings after count fo bo ids values:=by
    refine ⟨by rw [env];exact h.bindings.lookup,?_,h.bindings.distinct,?_⟩
    · intro v hv
      refine ⟨(h.bindings.slots v hv).storable,?_⟩
      rw [objects _ (h.well.objectIds _ _ (h.bindings.slots v hv).object) (h.separate v hv).symm]
      exact (h.bindings.slots v hv).object
    · intro v hv;exact lt_of_lt_of_le (h.bindings.bound v hv) nextScope
  exact ⟨array,bindings,h.parameters,h.separate,well,scope.trans h.scope,h.active,h.fresh.trans nextObject,h.born⟩

theorem Profile.canonical_selected {F : Type} (p : Profile) (context : Context F) (pinned : context.program=p.program) :
    findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast:=by
  rw [pinned];cases p <;> rfl

def canonicalStatement : Stmt:=.expression (.call "canonical_sign" [.variable "p"])

theorem source_canonical : (ProductRow.items loopBody)[11]?=some canonicalStatement:=rfl

theorem BodyView.canonical_execution {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo j cutoff : Nat}
    {ids : Var → Nat} {memory : Nat → Nat}
    (h : BodyView before input fo bo 5 j cutoff ids (dividedValues input j) (rawStores memory (12*j) (input.profile.encoded j)))
    (pinned : context.program=input.profile.program) (zero : ∀i<12,memory (12*j+i)=0) :
    ∃after,Exec context before canonicalStatement .normal after ∧ Every context before canonicalStatement .normal after ∧
      BodyView after input fo bo 5 j cutoff ids (dividedValues input j) (readyCell memory (12*j) (input.profile.encoded j)) ∧
      ApplicationBirthFrame.Frame cutoff before after [input.object]:=by
  have shape:=input.profile.shape
  have bound : 12*j+6≤12*input.profile.grid:=by have a:=h.active;omega
  have digits : ∀i<5,rawStores memory (12*j) (input.profile.encoded j) (12*j+i)<1000000000:=by
    intro i hi
    rw [rawStores_word memory (12*j) _ i (by omega) zero]
    unfold InputCell.rawCell
    rw [Function.update_of_ne (by omega : i≠5)]
    exact InputCell.packed_digit_bound _ _ (InputCell.scaled_value_bound _ (input.profile.encoded_bound j h.active).le) hi
  have selected:=input.profile.canonical_selected context pinned
  obtain ⟨after,called,array,frame⟩:=CanonicalSource.canonical_sign_call_framed context selected before input.object (12*input.profile.grid) (12*j) _ h.well h.array bound digits
  have pointerRead : Eval context before (.variable "p") (.pointer (wordPointer input.object (12*j))) before:=by
    simpa [temporaryName,dividedValues,branchValues,plannedValues] using h.variable context .p (by norm_num [Active,localIndex])
  have args : Args context before [.variable "p"] [.pointer (wordPointer input.object (12*j))] before:=by
    apply Args.ordered (order:=[(0,.variable "p")]) (evaluated:=[(0,.pointer (wordPointer input.object (12*j)))])
    · exact List.Perm.refl _
    · exact .cons pointerRead .nil
    · change List.Forall₂ _ [0] _;exact .cons rfl .nil
  have run : Exec context before canonicalStatement .normal after:=.expression (.call args called)
  have every:=every_expression_call (by intro e he;simp only [List.mem_singleton] at he;subst e;trivial) args
    (fun state result actual=> CanonicalSource.call_unique selected called actual)
  have birth : ApplicationBirthFrame.Frame cutoff before after [input.object]:=
    ⟨frame.well,h.fresh.trans frame.nextObject,frame.nextObject,frame.nextScope,frame.mode,frame.foreign,
      fun id old absent=> frame.objects id (lt_of_lt_of_le old h.fresh) (by simpa only [List.mem_singleton] using absent)⟩
  exact ⟨after,run,every,h.reframe array frame.environment frame.scope frame.well frame.nextObject frame.nextScope frame.objects,birth⟩

#print axioms BodyView.canonical_execution
end RH080Next.FFTPV.InputLoader
