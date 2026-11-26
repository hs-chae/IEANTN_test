/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveHeaderBindings
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ProductInner ApplicationBirthFrame
namespace Header

/-- Header locals exist only after their real source declarations. -/
structure View {F : Type} (state : State F) {total : Nat} (buffers : Buffers total)
    (start index step n count : Nat) (ids : LoopVar → Nat) (owner : Nat)
    (input table output work : Nat → Nat) : Prop where
  bindings : PartialBindings state count ids owner (loopValue buffers start index step n 0)
  arrays : ∀r, WordArrayRep state (buffers.object r) (buffers.length r)
    (bufferData input table output work r)
  well : WellScoped state
  scope : state.scope=owner

theorem View.initial {F : Type} {state : State F} {total : Nat} {buffers : Buffers total}
    {start index step n owner : Nat} {parameterIds : Var → Nat}
    {input table output work : Nat → Nat}
    (parameters : Locals state name type parameterIds owner
      (value (buffers.object .output) (buffers.object .input) (buffers.object .twiddle)
        (buffers.object .work) start index step n total))
    (arrays : ∀r, WordArrayRep state (buffers.object r) (buffers.length r)
      (bufferData input table output work r))
    (well : WellScoped state) (scope : state.scope=owner) :
    View state buffers start index step n 0 (Sum.elim parameterIds (fun _=>0)) owner
      input table output work := by
  refine ⟨⟨?_,?_,?_,parameters.bound⟩,arrays,well,scope⟩
  · intro v hv
    cases v with
    | inl p => exact parameters.lookup p
    | inr p => exact False.elim (by change localIndex p<0 at hv; omega)
  · intro v hv
    cases v with
    | inl p => exact parameters.slots p
    | inr p => exact False.elim (by change localIndex p<0 at hv; omega)
  · intro v w hv hw same
    cases v with
    | inl p =>
      cases w with
      | inl q => exact congrArg Sum.inl (parameters.distinct same)
      | inr q => exact False.elim (by change localIndex q<0 at hw; omega)
    | inr p => exact False.elim (by change localIndex p<0 at hv; omega)

theorem View.declare {F : Type} {before after : State F} {total : Nat} {buffers : Buffers total}
    {start index step n count owner : Nat} {ids : LoopVar → Nat}
    {input table output work : Nat → Nat} {next : LocalVar}
    (h : View before buffers start index step n count ids owner input table output work)
    (indexNext : localIndex next=count)
    (d : Declaration before after (localName next) (localType next)
      (loopValue buffers start index step n 0 (.inr next)))
    (declared : before.declare (localType next) (localName next)
      (some (loopValue buffers start index step n 0 (.inr next)))=some after) :
    View after buffers start index step n (count+1)
      (Function.update ids (.inr next) before.nextObject) owner input table output work :=
  ⟨h.bindings.declare_next h.well h.scope indexNext d,
    fun r=>array_declare_old h.well (h.arrays r) d,
    wellScoped_declare h.well declared,d.scope.trans h.scope⟩

theorem View.after_call {F : Type} {before after : State F} {total : Nat} {buffers : Buffers total}
    {start index step n count owner : Nat} {ids : LoopVar → Nat}
    {input table output work input' table' output' work' : Nat → Nat}
    (h : View before buffers start index step n count ids owner input table output work)
    (frame : MultiplyCall.CallerFrame before after [buffers.object .output,buffers.object .work])
    (arrays : ∀r, WordArrayRep after (buffers.object r) (buffers.length r)
      (bufferData input' table' output' work' r)) :
    View after buffers start index step n count ids owner input' table' output' work' := by
  refine ⟨⟨?_,?_,h.bindings.distinct,h.bindings.bound.trans_le frame.frame.nextScope⟩,
    arrays,frame.frame.well,frame.scope.trans h.scope⟩
  · intro v hv
    rw [frame.environment]
    exact h.bindings.lookup v hv
  · intro v hv
    have old := h.bindings.slots v hv
    have outside : ids v∉[buffers.object .output,buffers.object .work] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (eq|eq)
      · exact array_ne_slot (h.arrays .output) old eq.symm
      · exact array_ne_slot (h.arrays .work) old eq.symm
    exact ⟨old.storable,(frame.frame.outside _ (h.well.objectIds _ _ old.object) outside).trans old.object⟩

theorem View.complete {F : Type} {state : State F} {total : Nat} {buffers : Buffers total}
    {start index step n owner : Nat} {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : View state buffers start index step n 5 ids owner input table output work) :
    LoopView state buffers start index step n ids owner 0 input table output work :=
  ⟨h.bindings.complete,h.arrays,h.well,Nat.zero_le _⟩

#print axioms View.initial
#print axioms View.declare
#print axioms View.after_call
#print axioms View.complete
end Header
end RH080Next.FFTPV.RecursiveSource
