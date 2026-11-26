/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveIndexExpressions
import FFTRecursiveLoopBindings
import FFTRecursiveButterflyIndices
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- The three actual source pointer initializer expressions evaluate from real
loop-variable slots and caller buffers, with every intermediate u64/product
and pointer-validity bound proved. -/
theorem butterfly_pointer_expressions {F : Type} (context : Context F) {state : State F}
    {total : Nat} {buffers : Buffers total} {start index step n half j owner : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : LoopView state buffers start index step n ids owner j input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half) :
    Eval context state butterflyA (.pointer (wordPointer (buffers.object .output) ((start+j)*12))) state ∧
    Eval context state butterflyB (.pointer (wordPointer (buffers.object .output) ((start+j+half)*12))) state ∧
    Eval context state butterflyW (.pointer (wordPointer (buffers.object .twiddle) ((j*(total/n))*12))) state := by
  have bounds := shape.scalar_bounds
  have indices := butterfly_indices shape split active
  have offsets := butterfly_word_offsets shape split active
  have halfEq : n/2=half := by omega
  have halfFit : half<2^64 := by omega
  have jFit : j<2^64 := by omega
  have sumFit : start+j<2^64 := by omega
  have rightFit : start+j+half<2^64 := by omega
  have strideFit : total/n<2^64 := by rw [shape.stride_exact];exact bounds.2.2.1
  have evStart := Eval.variable (context:=context) (h.bindings.lookup (.inl .start)) (h.bindings.read (.inl .start))
  have evJ := Eval.variable (context:=context) (h.bindings.lookup (.inr .j)) (h.bindings.read (.inr .j))
  have evHalf : Eval context state (.variable "half") (.integer (integer64 half)) state := by
    simpa [loopName,localName,loopValue,halfEq] using
      (Eval.variable (context:=context) (h.bindings.lookup (.inr .half)) (h.bindings.read (.inr .half)))
  have evStride := Eval.variable (context:=context) (h.bindings.lookup (.inr .stride)) (h.bindings.read (.inr .stride))
  have sumEval := add_expr_eval context evStart evJ bounds.1 jFit sumFit
  have rightEval := add_expr_eval context sumEval evHalf sumFit halfFit rightFit
  have twiddleEval := mul_expr_eval context evJ evStride jFit strideFit offsets.2.2.1
  have evOutput := Eval.variable (context:=context) (h.bindings.lookup (.inl .output)) (h.bindings.read (.inl .output))
  have evTwiddle := Eval.variable (context:=context) (h.bindings.lookup (.inl .twiddle)) (h.bindings.read (.inl .twiddle))
  refine ⟨?_,?_,?_⟩
  · exact cell_pointer_eval context evOutput sumEval (h.arrays .output) sumFit offsets.1
      (by have hb := buffers.outputBound;omega)
  · exact cell_pointer_eval context evOutput rightEval (h.arrays .output) rightFit offsets.2.1
      (by have hb := buffers.outputBound;omega)
  · exact cell_pointer_eval context evTwiddle twiddleEval (h.arrays .twiddle) offsets.2.2.1 offsets.2.2.2
      (by have hb := buffers.twiddleBound;omega)

#print axioms butterfly_pointer_expressions
end RH080Next.FFTPV.RecursiveSource
