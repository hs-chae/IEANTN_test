/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTEncodedSelectorCall
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.FFTPV.EncodedSelector
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals

theorem result_eq_getD {tree : Tree} {values : List Nat} (cover : Covers tree 0 values)
    (length fallback j : Nat) (size : values.length=length) : result length fallback tree j=values[j]?.getD fallback:=by
  by_cases inside : j<length
  · have bound : j<values.length:=by simpa only [size] using inside
    have value:=cover.value_eq j bound
    simp only [Nat.zero_add,List.getElem?_eq_getElem bound,Option.getD_some] at value ⊢
    simpa only [result,show ¬length≤j from by omega,↓reduceIte] using value
  · have missing : values[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [result,show length≤j from by omega,↓reduceIte,missing,Option.getD_none]

theorem w4_safe : w4Tree.Safe:=by
  apply build_safe 2520 0 RH080Next.WindowPV.Data.encoded
  · rw [RH080Next.WindowPV.Data.encoded_length]
    norm_num
  · intro v member
    have small:=of_decide_eq_true ((List.all_eq_true.mp RH080Next.WindowPV.Data.encoded_all_fit) v member)
    exact small.trans (by norm_num [RH080Next.WindowPV.Data.scale])

theorem fap_safe : fapTree.Safe:=by
  apply build_safe 400 0 RH080Next.FapPV.Data.encoded
  · rw [RH080Next.FapPV.Data.encoded_length]
    norm_num
  · intro v member
    have small:=of_decide_eq_true ((List.all_eq_true.mp RH080Next.FapPV.Data.encoded_all_fit) v member)
    exact small.trans (by norm_num [RH080Next.FapPV.Data.scale])

def Correct {F : Type} (context : Context F) (before : State F) (j value : Nat) : Prop:=
  ∃after,Call context "encoded_node" [.integer (integer64 j)] before (.value (.integer (integer64 value))) after ∧
    MultiplyCall.CallerFrame before after [] ∧
    ∀after' output,Call context "encoded_node" [.integer (integer64 j)] before output after' →
      output=.value (.integer (integer64 value)) ∧ after'=after

/-- Actual typed source execution supplies the exact original locked w4 input
coefficient, including its documented zero-extension fallback. This input
lookup contract is separate from the later FFT numerical-result theorem. -/
theorem w4_encoded_node_correct {F : Type} (context : Context F)
    (pinned : context.program=FFTRecursivePV.program) (before : State F) (j : Nat)
    (well : WellScoped before) (fits : j<2^64) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      Correct context before j (RH080Next.WindowPV.Data.encodedNode j):=by
  have selected : findFunction context.program "encoded_node"=some (function 2520 10000000000000000 w4Tree):=by
    rw [pinned]
    change some FFTRecursivePV.encoded_node_ast=some _
    rw [w4_actual_function]
  have called:=encoded_node_call context 2520 10000000000000000 w4Tree selected before j (by norm_num) (by norm_num) w4_safe well fits
  have mapped : result 2520 10000000000000000 w4Tree j=RH080Next.WindowPV.Data.encodedNode j:=
    result_eq_getD w4_covers _ _ _ RH080Next.WindowPV.Data.encoded_length
  rw [mapped] at called
  exact ⟨FFTRecursivePV.actual_source_syntax,called⟩

/-- The separate actual Fap source selector supplies the original finite-slab
profile (400 inputs at mesh80), not the global w4 profile. -/
theorem fap_encoded_node_correct {F : Type} (context : Context F)
    (pinned : context.program=FapFFTRecursivePV.program) (before : State F) (j : Nat)
    (well : WellScoped before) (fits : j<2^64) :
    Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      Correct context before j (RH080Next.FapPV.Data.encodedNode j):=by
  have selected : findFunction context.program "encoded_node"=some (function 400 10000000000000000 fapTree):=by
    rw [pinned]
    change some FapFFTRecursivePV.encoded_node_ast=some _
    rw [fap_actual_function]
  have called:=encoded_node_call context 400 10000000000000000 fapTree selected before j (by norm_num) (by norm_num) fap_safe well fits
  have mapped : result 400 10000000000000000 fapTree j=RH080Next.FapPV.Data.encodedNode j:=
    result_eq_getD fap_covers _ _ _ RH080Next.FapPV.Data.encoded_length
  rw [mapped] at called
  exact ⟨FapFFTRecursivePV.actual_source_syntax,called⟩

#print axioms w4_encoded_node_correct
#print axioms fap_encoded_node_correct
end RH080Next.FFTPV.EncodedSelector
