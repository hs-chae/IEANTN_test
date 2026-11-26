/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCopyGenericCall
import FFTPureDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CopyLoop
open GoldbachDirect GoldbachDirect.Semantics WordArrays PureDeterminism
open SourceLocals SourceScalarSlots SourceBindings

private theorem condition_execution {F : Type} (context : Context F) {before : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j) :
    Eval context before condition (.integer (.boolean (decide (j < length)))) before := by
  have computed : Integer.binary .lt (integer64 j) (integer64 length) =
      some (.boolean (decide (j < length))) := by
    change some (Integer.boolean ((Integer.cast .u64 (j:Int)).toInt <
      (Integer.cast .u64 (length:Int)).toInt)) = _
    rw [cast64_exact j (lt_of_le_of_lt h.active h.fits), cast64_exact length h.fits,
      integer64_toInt, integer64_toInt]
    congr 2
    simp
  exact .binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
    (.variable (h.locals.lookup Var.n) (h.locals.read Var.n))
    (by simp only [value, binary, computed, Option.map_some])

private theorem condition_pure : SourcePure.CallFree condition := by
  simp [condition, ZeroLoop.condition, SourcePure.CallFree]

/-- Every permitted execution of the actual source block has the proved next
copy prefix; it is independent of evaluation order within pure expressions. -/
theorem block_postcondition {F : Type} {context : Context F} {before after : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat} {flow : Flow}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j)
    (hj : j < length) (run : Exec context before loopBody flow after) :
    flow = .normal ∧ View after outObject outLength outStart inObject inLength inStart length owner ids old input (j+1) := by
  obtain ⟨expected, known, view⟩ := block_execution context h hj
  have pure : ∀s ∈ [storeStmt, increment], Simple s := by
    simp [Simple, storeStmt, increment, ZeroLoop.increment, SourcePure.CallFree]
  obtain ⟨eqFlow, eqState⟩ := block_unique pure known run
  exact ⟨eqFlow.symm, eqState ▸ view⟩

/-- Universal partial correctness of the actual copy while loop. Every allowed
execution has normal flow, copies the exact slice, and preserves its input.
Existence/termination is independently supplied by loop_execution. -/
theorem loop_postcondition {F : Type} {context : Context F} (steps : Nat)
    {before after : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat} {flow : Flow}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j)
    (remaining : j+steps = length) (run : Exec context before loop flow after) :
    flow = .normal ∧ View after outObject outLength outStart inObject inLength inStart length owner ids old input length := by
  induction steps generalizing before after j flow with
  | zero =>
    have he : j = length := by omega
    subst j
    change Exec context before (.whileLoop condition loopBody) flow after at run
    cases run with
    | whileFalse tested truth =>
      obtain ⟨_, rfl⟩ := eval_unique condition_pure (condition_execution context h) tested
      exact ⟨rfl, h⟩
    | whileNext tested truth body rest =>
      obtain ⟨rfl, _⟩ := eval_unique condition_pure (condition_execution context h) tested
      simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed] at truth
    | whileContinue tested truth body rest =>
      obtain ⟨rfl, _⟩ := eval_unique condition_pure (condition_execution context h) tested
      simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed] at truth
    | whileBreak tested truth body =>
      obtain ⟨rfl, _⟩ := eval_unique condition_pure (condition_execution context h) tested
      simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed] at truth
    | whileExit tested truth body abrupt =>
      obtain ⟨rfl, _⟩ := eval_unique condition_pure (condition_execution context h) tested
      simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed] at truth
  | succ steps ih =>
    have hj : j < length := by omega
    change Exec context before (.whileLoop condition loopBody) flow after at run
    cases run with
    | whileFalse tested truth =>
      obtain ⟨rfl, _⟩ := eval_unique condition_pure (condition_execution context h) tested
      simp [Value.truth, Integer.truth, Integer.boolean, Integer.toInt, IntKind.signed, hj] at truth
    | whileNext tested truth body rest =>
      obtain ⟨_, rfl⟩ := eval_unique condition_pure (condition_execution context h) tested
      have post := block_postcondition h hj body
      exact ih post.2 (by omega) rest
    | whileContinue tested truth body rest =>
      obtain ⟨_, rfl⟩ := eval_unique condition_pure (condition_execution context h) tested
      have post := block_postcondition h hj body
      cases post.1
    | whileBreak tested truth body =>
      obtain ⟨_, rfl⟩ := eval_unique condition_pure (condition_execution context h) tested
      have post := block_postcondition h hj body
      cases post.1
    | whileExit tested truth body abrupt =>
      obtain ⟨_, rfl⟩ := eval_unique condition_pure (condition_execution context h) tested
      exact False.elim (abrupt.1 (block_postcondition h hj body).1)

/-- The exact copied destination slice follows for every source-model run. -/
theorem loop_every_output {F : Type} {context : Context F} {before after : State F}
    {outObject outLength outStart inObject inLength inStart length owner j : Nat}
    {ids : Var → Nat} {old input : Nat → Nat} {flow : Flow}
    (h : View before outObject outLength outStart inObject inLength inStart length owner ids old input j)
    (run : Exec context before loop flow after) :
    flow = .normal ∧
      (∀i, i < length → after.load (wordPointer outObject (outStart+i)) = some (.integer (integer64 (input i)))) ∧
      (∀i, i < length → after.load (wordPointer inObject (inStart+i)) = some (.integer (integer64 (input i)))) ∧
      ScanFrame.Frame before after [ids Var.j, outObject] := by
  obtain ⟨normal, result⟩ := loop_postcondition (length-j) h (by have hj := h.active; omega) run
  refine ⟨normal, ?_, ?_, loop_frame h run⟩
  · intro i hi
    have hib : outStart+i < outLength := by have hb := h.outBound; omega
    have load := word_load result.output hib
    simpa [prefixData, show outStart ≤ outStart+i ∧ outStart+i < outStart+length by omega] using load
  · obtain ⟨data, rep, values⟩ := result.source
    intro i hi
    have hib : inStart+i < inLength := by have hb := h.inBound; omega
    simpa only [values i hi] using word_load rep hib

#print axioms block_postcondition
#print axioms loop_postcondition
#print axioms loop_every_output
end RH080Next.FFTPV.CopyLoop
