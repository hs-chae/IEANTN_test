/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- Exact same-allocation preservation, stronger than the whole-object caller
frame. Every word outside the six-word output slice is literally unchanged. -/
theorem finalData_outside (input : Input) (index : Nat)
    (outside : index< input.layout.start .out ∨ input.layout.start .out+6≤ index) :
    finalData input index=input.old (input.layout.object .out) index := by
  have signDifferent : index≠input.layout.start .out+5:=by omega
  have digitOutside : ¬(input.layout.start .out≤ index ∧ index< input.layout.start .out+5):=by omega
  simp only [finalData,CanonicalSource.canonicalData,Function.update_of_ne signDifferent]
  unfold rawData
  split_ifs <;> simp [signedData,Function.update_of_ne signDifferent,currentData,digitOutside]

/-- An observed actual fixed_add Call preserves every caller word outside the
output slice, including when output and both inputs share one allocation. -/
theorem fixed_add_call_slice_frame {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_add"=some fixed_add_ast)
    (compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (canonicalSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    (before after : State F) (input : Input) (well : WellScoped before)
    (rep : ∀r,WordArrayRep before (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r)))
    (result : CallResult) (run : Call context "fixed_add" (arguments input) before result after)
    (index : Nat) (bound : index< input.layout.length (input.layout.object .out))
    (outside : index< input.layout.start .out ∨ input.layout.start .out+6≤ index) :
    after.load (wordPointer (input.layout.object .out) index)=
      before.load (wordPointer (input.layout.object .out) index) := by
  obtain ⟨⟨known,knownRun,post,frame,every⟩,correct⟩:=fixed_add_total context selected compareSelected canonicalSelected before input well rep
  obtain ⟨resultEq,stateEq⟩:=every after result run
  cases stateEq
  rw [word_load post bound,word_load (rep .out) bound,finalData_outside input index outside]

#print axioms finalData_outside
#print axioms fixed_add_call_slice_frame
end RH080Next.FFTPV.AddSource
