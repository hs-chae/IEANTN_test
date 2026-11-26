/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootFrames
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- Extract the real store from a source assignment with independently known
pure expression/place interpretations, and prove its actual application frame. -/
theorem assignment_full_frame {F : Type} {context : Context F} {before after : State F}
    {left right : Expr} {pointer : Pointer} {value : Value} {object : Nat}
    (well : WellScoped before) (rightPure : SourcePure.CallFree right) (leftPure : SourcePure.CallFree left)
    (rightEval : Eval context before right value before) (leftPlace : Place context before left pointer before)
    (objectEq : pointer.object=object) (run : Exec context before (.assign left right) .normal after) :
    IncrementSource.FullCallerFrame before after object := by
  cases run with
  | assign evaluated placed stored=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique rightPure rightEval evaluated
    obtain ⟨rfl,rfl⟩:=PureDeterminism.place_unique leftPure leftPlace placed
    have fields:=SourceLocals.store_frame stored
    apply full_caller_frame fields.1 fields.2.2.1
    exact ApplicationBirthFrame.store_frame before.nextObject [object] well (le_refl _)
      (Or.inl (by simp [objectEq])) stored

/-- A real pure-RHS declaration allocates its application slot and preserves
all previous caller objects; scope and birth clocks are proved from declare. -/
theorem declaration_birth_frame {F : Type} {context : Context F} {before after : State F}
    {ctype : CType} {cname : String} {right : Expr} {value : Value} {object : Nat}
    (well : WellScoped before) (rightPure : SourcePure.CallFree right)
    (rightEval : Eval context before right value before)
    (run : Exec context before (.declare ctype cname (some right)) .normal after) :
    ApplicationBirthFrame.Frame before.nextObject before after [object] ∧ after.scope=before.scope := by
  cases run with
  | declareSome evaluated declared=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique rightPure rightEval evaluated
    exact ⟨ApplicationBirthFrame.declare_frame _ _ well (le_refl _) declared,(SourceLocals.declare_frame declared).1⟩

/-- Framing the actual literal-index store exposed by the initializer's
existing execution theorem does not assume any successful program effect. -/
theorem literal_store_framed {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner statusId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ScaleView before input owner statusId ids data) (p : Param) (hp : PointerParam p)
    (offset value : Nat) (bound : pointerStart input p+offset< input.layout.size) (offset64 : offset<2^64) (value64 : value<2^64) :
    ∃after,Exec context before (literalStore p offset value) .normal after ∧
      Every context before (literalStore p offset value) .normal after ∧
      ScaleView after input owner statusId ids (Function.update data (pointerStart input p+offset) value) ∧
      IncrementSource.FullCallerFrame before after input.layout.object := by
  obtain ⟨after,run,post,scope⟩:=literal_store_execution context h p hp offset value bound offset64 value64
  have variableEval : Eval context before (.variable (paramName p))
      (.pointer (wordPointer input.layout.object (pointerStart input p))) before:=by
    rcases hp with rfl|rfl <;> exact .variable (h.params.locals.lookup _) (h.params.locals.read _)
  have literalEval : Eval context before (.literal (.integer value "ULL")) (.integer (integer64 value)) before:=
    .literal _ _ _ (by have small : value<18446744073709551616:=value64;simp [Literal.value,integer64,small])
  have place : Place context before (.index (.variable (paramName p)) (.literal (.integer offset "ULL")))
      (wordPointer input.layout.object (pointerStart input p+offset)) before:=.index variableEval
        (.literal _ _ _ (by have small : offset<18446744073709551616:=offset64;simp [Literal.value,integer64,small]))
        (slice_pointer_add h.params.array bound)
  exact ⟨after,run,every_pure (by simp [literalStore,PureDeterminism.Simple,SourcePure.CallFree]) run,post,assignment_full_frame h.params.well (by trivial) (by trivial) literalEval place rfl run⟩

#print axioms assignment_full_frame
#print axioms declaration_birth_frame
#print axioms literal_store_framed
end RH080Next.FFTPV.RootSource
