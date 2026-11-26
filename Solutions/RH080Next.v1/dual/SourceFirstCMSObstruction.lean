/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CMSWeakDuality
import CompactDualSourceFirst

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open RH080.Dual
namespace RH080Next.Dual

/-- The existing actual-C norm cap now gives a lower functional bound on the
full CMS class. There is no L1 hypothesis on the Fourier transform. -/
theorem source_first_full_cms_lower_bound
    (F : ℝ → ℝ) (hF : Integrable F) (hcont : ContinuousAt F 0)
    (heven : Function.Even F)
    (hpen : Integrable (exteriorPositive (cosineTransform F)))
    (hden : 0 < F 0 - (36/11 : ℝ) * (∫ v in exterior, max 0 (cosineTransform F v))) :
    (100/123 : ℝ) ≤ (∫ x : ℝ, |F x|) /
      (F 0 - (36/11 : ℝ) * (∫ v in exterior, max 0 (cosineTransform F v))) := by
  have hh := functional_lower_bound_even_cms F compactStep (36/11) (123/100)
    hF compactStep_integrable hcont heven hpen
    (fun v hv => compactStep_center v (le_of_not_gt hv))
    (fun v _ => (compactStep_bounds v).1) (fun v _ => (compactStep_bounds v).2)
    source_first_compact_global (by norm_num) hden
  norm_num at hh ⊢
  exact hh

/-- This excludes 0.8 in this functional, not in every possible RH argument. -/
theorem source_first_full_cms_excludes_four_fifths
    (F : ℝ → ℝ) (hF : Integrable F) (hcont : ContinuousAt F 0)
    (heven : Function.Even F)
    (hpen : Integrable (exteriorPositive (cosineTransform F)))
    (hden : 0 < F 0 - (36/11 : ℝ) * (∫ v in exterior, max 0 (cosineTransform F v))) :
    (4/5 : ℝ) < (∫ x : ℝ, |F x|) /
      (F 0 - (36/11 : ℝ) * (∫ v in exterior, max 0 (cosineTransform F v))) :=
  lt_of_lt_of_le (by norm_num : (4/5 : ℝ) < 100/123)
    (source_first_full_cms_lower_bound F hF hcont heven hpen hden)

/-- The source checker, actual source-AST run, serialization model and full-class
functional consequence are preserved together on the accepted path. Precise
compiler/ABI/libc/OS/hardware interpretation contracts remain external. -/
theorem source_first_full_cms_result :
    RH080PV.Verified.SourceFirstOutput ∧
    ∀ (F : ℝ → ℝ), Integrable F → ContinuousAt F 0 → Function.Even F →
      Integrable (exteriorPositive (cosineTransform F)) →
      0 < F 0 - (36/11 : ℝ) * (∫ v in exterior, max 0 (cosineTransform F v)) →
      (100/123 : ℝ) ≤ (∫ x : ℝ, |F x|) /
        (F 0 - (36/11 : ℝ) * (∫ v in exterior, max 0 (cosineTransform F v))) :=
  ⟨RH080PV.Verified.actual_source_first_output, source_first_full_cms_lower_bound⟩

#print axioms source_first_full_cms_lower_bound
#print axioms source_first_full_cms_excludes_four_fifths
#print axioms source_first_full_cms_result
end RH080Next.Dual
