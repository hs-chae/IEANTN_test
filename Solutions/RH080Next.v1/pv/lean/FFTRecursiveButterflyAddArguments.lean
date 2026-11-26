/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyBirth
import FFTRecursivePointerOffsets
import FFTComplexArguments
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceBindings

def addValues {total : Nat} (buffers : Buffers total) (start half j : Nat) (i : Fin 4) : List Value :=
  [.pointer (wordPointer (if i.val<2 then buffers.object .work else buffers.object .output)
      (if i.val<2 then 48+6*(i.val%2) else (start+j+half)*12+6*(i.val%2))),
   .pointer (wordPointer (buffers.object .output) ((start+j)*12+6*(i.val%2))),
   .pointer (wordPointer (buffers.object .work) (160+6*(i.val%2))),
   .integer (integer64 (if i.val<2 then 0 else 1))]

/-- Actual source expressions for each of the four fixed_add calls, evaluated
from real source pointer/loop bindings and real buffer/pointer extents. -/
theorem butterfly_add_arguments {F : Type} (context : Context F) {before : State F}
    {total : Nat} {buffers : Buffers total} {start index step n half j owner pointerOwner : Nat}
    {ids : LoopVar → Nat} {pids : PointerVar → Nat} {input table output work : Nat → Nat}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (pointers : Locals before pointerName pointerType pids pointerOwner (pointerValue buffers start n half j))
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half) (i : Fin 4) :
    Args context before (butterflyArguments ⟨i.val+1,by omega⟩) (addValues buffers start half j i) before := by
  have indices := butterfly_indices shape split active
  have evA := Eval.variable (context:=context) (pointers.lookup .a) (pointers.read .a)
  have evB := Eval.variable (context:=context) (pointers.lookup .b) (pointers.read .b)
  have evTemp := Eval.variable (context:=context) (h.bindings.lookup (.inr .temp)) (h.bindings.read (.inr .temp))
  have evWork := Eval.variable (context:=context) (h.bindings.lookup (.inl .work)) (h.bindings.read (.inl .work))
  have a6 := word_offset_eval context evA (h.arrays .output) (offset:=6) (by norm_num)
    (by have hb := buffers.outputBound;omega)
  have b6 := word_offset_eval context evB (h.arrays .output) (offset:=6) (by norm_num)
    (by have hb := buffers.outputBound;omega)
  have t6 := word_offset_eval context evTemp (h.arrays .work) (offset:=6) (by norm_num)
    (by have hb := buffers.workBound;omega)
  have w48 := word_offset_eval context evWork (h.arrays .work) (offset:=48) (by norm_num)
    (by have hb := buffers.workBound;omega)
  have w54 := word_offset_eval context evWork (h.arrays .work) (offset:=54) (by norm_num)
    (by have hb := buffers.workBound;omega)
  have zero : Eval context before (literal 0) (.integer (integer64 0)) before := .literal _ _ _ (by rfl)
  have one : Eval context before (literal 1) (.integer (integer64 1)) before := .literal _ _ _ (by rfl)
  fin_cases i
  · simpa [butterflyArguments,addValues,pointerOffset,loopName,localName,pointerName,loopValue,pointerValue,name] using ComplexSource.four_arguments w48 evA evTemp zero
  · simpa [butterflyArguments,addValues,pointerOffset,loopName,localName,pointerName,loopValue,pointerValue,name] using ComplexSource.four_arguments w54 a6 t6 zero
  · simpa [butterflyArguments,addValues,pointerOffset,loopName,localName,pointerName,loopValue,pointerValue,name] using ComplexSource.four_arguments evB evA evTemp one
  · simpa [butterflyArguments,addValues,pointerOffset,loopName,localName,pointerName,loopValue,pointerValue,name] using ComplexSource.four_arguments b6 a6 t6 one

#print axioms butterfly_add_arguments
end RH080Next.FFTPV.RecursiveSource
