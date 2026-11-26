/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLoopBindings
import FFTRecursiveBindingsFrame
import FFTRecursiveIndexExpressions
import FFTRecursiveSegments
import FFTFixedMultiplySuffixBindings
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays PureDeterminism
open SourceLocals SourceScalarSlots SourceBindings ProductInner ApplicationBirthFrame

/-- Actual u64 comparison in the source while condition, from real source
counter/half slots. Both possible operand orders have the same pure value. -/
theorem loop_condition_eval {F : Type} (context : Context F) {state : State F}
    {total : Nat} {buffers : Buffers total} {start index step n owner j : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : LoopView state buffers start index step n ids owner j input table output work)
    (shape : IndexShape start index step n total) :
    Eval context state loopCondition (.integer (.boolean (decide (j<n/2)))) state := by
  have nFit := shape.scalar_bounds.2.2.2.1
  have halfFit : n/2<2^64 := by omega
  have jFit : j<2^64 := by have bound := h.active;omega
  have computed : Integer.binary .lt (integer64 j) (integer64 (n/2)) =
      some (.boolean (decide (j<n/2))) := by
    change some (Integer.boolean (decide ((Integer.cast .u64 (j:Int)).toInt <
      (Integer.cast .u64 (((n/2:Nat):Int))).toInt))) = _
    rw [cast64_exact j jFit,cast64_exact (n/2) halfFit,integer64_toInt,integer64_toInt]
    apply congrArg (fun b : Bool => some (Integer.boolean b))
    by_cases cmp : j<n/2
    · have castCmp : (j:Int)<(n:Int)/2 := by omega
      simp [cmp,castCmp]
    · have castCmp : ¬((j:Int)<(n:Int)/2) := by omega
      simp [cmp,castCmp]
  refine .binaryLR (.variable (h.bindings.lookup (.inr .j)) (h.bindings.read (.inr .j)))
    (.variable (h.bindings.lookup (.inr .half)) (h.bindings.read (.inr .half))) ?_
  simpa [binary,loopValue] using congrArg (Option.map Value.integer) computed

/-- The actual counter update stores j+1 in the true function-owned scalar
object and preserves all actual typed arrays and other source variables. -/
theorem loop_increment {F : Type} (context : Context F) {before : State F}
    {total : Nat} {buffers : Buffers total} {start index step n owner j : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (shape : IndexShape start index step n total) (active : j<n/2) :
    ∃after, NormalSegment context before [incrementJ] after ∧
      LoopView after buffers start index step n ids owner (j+1) input table output work ∧
      Frame before.nextObject before after [ids (.inr .j)] := by
  have nFit := shape.scalar_bounds.2.2.2.1
  have nextFit : j+1<2^64 := by omega
  have jFit : j<2^64 := by omega
  have storable := ZeroFrame.u64_storable (j+1) nextFit
  obtain ⟨after,stored⟩ := MultiplySuffix.scalar_store_exists (h.bindings.slots (.inr .j))
    (.integer (integer64 (j+1))) storable
  have evJ := Eval.variable (context:=context) (h.bindings.lookup (.inr .j)) (h.bindings.read (.inr .j))
  have evaluated := add_expr_eval context evJ (Eval.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
    jFit (by norm_num) nextFit
  have run : Exec context before incrementJ .normal after :=
    .assign evaluated (.variable (h.bindings.lookup (.inr .j))) stored
  have frame := ApplicationBirthFrame.store_frame before.nextObject [ids (.inr .j)] h.well
    (le_refl _) (Or.inl (by simp [scalarPointer])) stored
  have bindings := h.bindings.store (.inr .j) (.integer (integer64 (j+1))) storable stored
  have values : Function.update (loopValue buffers start index step n j) (.inr .j) (.integer (integer64 (j+1))) =
      loopValue buffers start index step n (j+1) := by
    funext v
    cases v with
    | inl v => cases v <;> simp [loopValue,Function.update]
    | inr v => cases v <;> simp [loopValue,Function.update]
  rw [values] at bindings
  have arrays : ∀r,WordArrayRep after (buffers.object r) (buffers.length r) (bufferData input table output work r) := by
    intro r
    have old := h.well.objectIds _ _ (h.arrays r).2.1
    have different := array_ne_slot (h.arrays r) (h.bindings.slots (.inr .j))
    exact ⟨frame.mode.trans (h.arrays r).1,
      (frame.outside _ old (by simpa using different)).trans (h.arrays r).2.1,(h.arrays r).2.2⟩
  refine ⟨after,NormalSegment.single run ?_,⟨bindings,arrays,frame.well,by omega⟩,frame⟩
  intro other flow otherRun
  obtain ⟨same,states⟩ := simple_unique (by trivial) run otherRun
  exact ⟨same.symm,states.symm⟩

#print axioms loop_condition_eval
#print axioms loop_increment
end RH080Next.FFTPV.RecursiveSource
