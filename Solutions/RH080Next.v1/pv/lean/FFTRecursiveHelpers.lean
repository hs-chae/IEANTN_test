/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexSourceFinal
import FFTCopyGenericCall
set_option autoImplicit false
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics

/-- These are actual function lookup equalities, not trusted helper-output
contracts. Each selected function is independently verified at its source. -/
structure Helpers {F : Type} (context : Context F) : Prop where
  recursive : findFunction context.program "fft_recursive" = some FFTRecursivePV.fft_recursive_ast
  copy : findFunction context.program "copy_words" = some copy_words_ast
  complex : findFunction context.program "complex_multiply" = some complex_multiply_ast
  multiply : findFunction context.program "fixed_multiply" = some fixed_multiply_ast
  zero : findFunction context.program "zero_words" = some zero_words_ast
  increment : findFunction context.program "increment_words" = some increment_words_ast
  add : findFunction context.program "fixed_add" = some fixed_add_ast
  compare : findFunction context.program "magnitude_compare" = some magnitude_compare_ast
  canonical : findFunction context.program "canonical_sign" = some FFTRecursivePV.canonical_sign_ast

/-- Literal function identities in the unchanged actual recursive C program. -/
theorem actual_helpers : Helpers CopyLoop.sourceContext :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms actual_helpers
end RH080Next.FFTPV.RecursiveSource
