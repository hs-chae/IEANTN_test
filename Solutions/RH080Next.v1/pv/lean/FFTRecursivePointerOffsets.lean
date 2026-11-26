/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveIndexExpressions
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- An actual source pointer offset is justified by the caller's real typed
array and literal width, not by an intended-buffer or successful-call premise. -/
theorem word_offset_eval {F : Type} (context : Context F) {state : State F}
    {expression : Expr} {object size start offset : Nat} {data : Nat → Nat}
    (source : Eval context state expression (.pointer (wordPointer object start)) state)
    (array : WordArrayRep state object size data) (fit : offset < 2^64)
    (bound : start+offset < size) :
    Eval context state (addExpr expression (literal offset))
      (.pointer (wordPointer object (start+offset))) state := by
  apply Eval.paren
  refine .binaryLR source
    (Eval.literal (.integer offset "ULL") _ (.integer (integer64 offset)) ?_) ?_
  · simp [Literal.value,integer64]
    omega
  · simpa only [binary,Option.map_some] using
      congrArg (Option.map Value.pointer) (slice_pointer_add array bound)

#print axioms word_offset_eval
end RH080Next.FFTPV.RecursiveSource
