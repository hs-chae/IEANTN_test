/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CompactDualVerified
import DualVerifiedSource

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080.Dual

/-- The actual C-source execution result supplies this all-real bound for the
actual inverse Fourier integral of the fixed rational step function. The proof
uses the generic mathematical bridge with the SOURCE-DERIVED integer cap;
it does not call the separate kernel-only sampleBound_all route. -/
theorem source_first_compact_global :
    ∀ x : ℝ, |cosineTransform compactStep x| ≤ (123/100 : ℝ) :=
  compact_kernel_global_of_grid
    (compact_grid_from_integer_caps RH080PV.Verified.actual_source_grid_cap)

/-- Complete source-linked Fourier-framework conclusion for the L1-Fourier
fragment. It does not assert a lower bound on prime gaps, does not exclude other
analytic methods, and does not silently assume a Fejer extension to Fourier
transforms outside L1. All actual Gaussian and compact-hat candidates fit this
fragment; the unrestricted paper result is a separate literature statement. -/
theorem source_first_compact_obstruction
    (F G : ℝ → ℝ) (hF : Integrable F) (hG : Integrable G) (hcont : Continuous F)
    (hfourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ))
    (hden : 0 < F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) :
    (4/5 : ℝ) < (∫ x : ℝ, |F x|) /
      (F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) :=
  compact_functional_obstruction
    (compact_grid_from_integer_caps RH080PV.Verified.actual_source_grid_cap)
    F G hF hG hcont hfourier hden

/-- The final result preserves source syntax, source AST execution, application
main/serialization, and the continuum mathematical consequence together. Precise
generic compiler/uint64 ABI/libc printf/OS/hardware applicability is the stated
external infrastructure boundary; it is not a new Lean axiom. -/
def SourceFirstFunctionalResult : Prop :=
  RH080PV.Verified.SourceFirstOutput ∧
  (∀ x : ℝ, |cosineTransform compactStep x| ≤ (123/100 : ℝ)) ∧
  (∀ (F G : ℝ → ℝ), Integrable F → Integrable G → Continuous F →
    (𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ)) →
    0 < F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v)) →
    (4/5 : ℝ) < (∫ x : ℝ, |F x|) /
      (F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))))

theorem actual_source_first_functional_result : SourceFirstFunctionalResult :=
  ⟨RH080PV.Verified.actual_source_first_output, source_first_compact_global,
    source_first_compact_obstruction⟩

#print axioms source_first_compact_global
#print axioms source_first_compact_obstruction
#print axioms actual_source_first_functional_result
end RH080.Dual
