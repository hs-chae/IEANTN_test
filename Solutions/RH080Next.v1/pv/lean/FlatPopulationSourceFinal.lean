/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FlatPopulationNorm
import FlatPopulationSource
import FlatPopulationMain
set_option autoImplicit false
namespace RH080Next.FlatPopulationPV
open MeasureTheory GoldbachDirect ScalarHost

/-- Source identity and execution of the application's actual printf harness.
Neither correct numerical output nor successful application effects are assumed. -/
def SourceOutput (out : Nat) : Prop :=
  Correspondence.SourceSyntaxCorresponds source program ∧
    mainOutput program (fun f => Execution.call 10000 f []) = some [out]

theorem actual_source_output : SourceOutput 1120475208606944546 :=
  ⟨actual_source_syntax,actual_main_output⟩

/-- Every output of this checked fixed-input source program has the advertised
mathematical enclosure. The actual executed numerator is consumed in the bound. -/
theorem source_output_periodic_norm (out : Nat) (h : SourceOutput out) :
    (∫ y in (0 : ℝ)..1, |Model.trigPolynomial y|) ≤
      (out : ℝ)/1000000000000000000 := by
  have he : some [1120475208606944546] = some [out] := actual_main_output.symm.trans h.2
  have ho : out = 1120475208606944546 := by simpa using (Option.some.inj he).symm
  rw [ho]
  simpa only [Model.normUpper_exact] using Model.periodic_norm_upper

/-- Completed source-first periodic-norm numerical provider. The real inverse
Fourier L1 identification is a separately declared analytic source boundary. -/
theorem source_first_periodic_norm :
    (∫ y in (0 : ℝ)..1, |Model.trigPolynomial y|) ≤
      (1120475208606944546 : ℝ)/1000000000000000000 :=
  source_output_periodic_norm _ actual_source_output

#print axioms actual_source_output
#print axioms source_output_periodic_norm
#print axioms source_first_periodic_norm
end RH080Next.FlatPopulationPV
