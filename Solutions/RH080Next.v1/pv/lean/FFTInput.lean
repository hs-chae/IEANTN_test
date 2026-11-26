/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTAST
import FFTRecursiveAST
import WindowExecution
import WindowData
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.Input

/-- Actual source AST identity, not equality of an independently invented table.
Both FFT source variants retain the original source-verified input provider. -/
theorem iterative_input_ast : FFTPV.encoded_node_ast=WindowPV.encoded_node_ast := by rfl

theorem recursive_input_ast : FFTRecursivePV.encoded_node_ast=WindowPV.encoded_node_ast := by rfl

theorem shared_multiply_ast : FFTRecursivePV.fixed_multiply_ast=FFTPV.fixed_multiply_ast := by rfl

theorem shared_zeroing_ast : FFTRecursivePV.zero_words_ast=FFTPV.zero_words_ast := by rfl

/-- Evaluate every actually used dynamic source lookup, traversing the input
literal list once. The list is original mathematical input, not a certificate of
an FFT output. The reused scalar execution model checks C word guards. -/
def sourceTable : List (Option Nat) := (List.range 2520).map fun j =>
  WindowPV.Execution.call 1000 "encoded_node" [j]

theorem sourceTable_exact : sourceTable=WindowPV.Data.encoded.map some := by
  decide +kernel

theorem source_lookup (j : Fin 2520) :
    WindowPV.Execution.call 1000 "encoded_node" [j.val]=some (WindowPV.Data.encodedNode j.val) := by
  have h := congrArg (fun l : List (Option Nat)=>l[j.val]?) sourceTable_exact
  have hj : j.val<WindowPV.Data.encoded.length := by
    simpa only [WindowPV.Data.encoded_length] using j.isLt
  simp only [sourceTable,List.getElem?_map,List.getElem?_range j.isLt,
    List.getElem?_eq_getElem hj,Option.map_some,Option.some.injEq] at h
  simpa only [WindowPV.Data.encodedNode,List.getElem?_eq_getElem hj,Option.getD_some] using h

#print axioms iterative_input_ast
#print axioms sourceTable_exact
#print axioms source_lookup
end RH080Next.FFTPV.Input
