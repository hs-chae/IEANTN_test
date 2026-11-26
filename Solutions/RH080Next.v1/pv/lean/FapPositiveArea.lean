/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScalarPositiveArea
import FapSourceFinal
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RH080Next.FapPV
open RH080Next.Explicit RH080Next.Primal RH080Next.ScalarPositiveArea

/-- Exact rational evaluation of the four-case mathematical cell integral.
This is not itself source PV; the actual C output is consumed below. -/
theorem actual_qPositiveArea : qPositiveArea Data.affineNodes 80 ≤
    (16297236881532502 : ℚ)/(80*10000000000000000) := by decide +kernel

private theorem positiveArea_hlen : 2≤Data.affineNodes.length := by
  rw [Data.affineNodes_length]
  norm_num

private theorem positiveArea_hlast : node Data.affineNodes
    (Data.affineNodes.length-1)=0 := by
  unfold node Data.affineNodes
  simp only [List.length_append,List.length_singleton,Nat.add_sub_cancel]
  rw [List.getD_append_right _ _ _ _ (le_refl _),Nat.sub_self]
  norm_num

/-- Every accepted output of the actual original scalar source bounds the
actual exterior positive-part integral, including all sign-changing cells. -/
theorem source_output_positive_leak (f0 area height v0 v1 mu2 maximum : ℕ)
    (h : SourceScalarOutput f0 area height v0 v1 mu2 maximum) :
    IEANTN.CMSFunctional.positiveLeak (affineSpectrum Data.affineNodes 80) ≤
      (area:ℝ)/(80*10000000000000000) := by
  have harea : area=16297236881532502 :=
    (source_output_finite_specification _ _ _ _ _ _ _ h).2.1.trans
      Model.positiveAreaNumerator_exact
  rw [positiveLeak_affineSpectrum_eq_nodalPositiveArea Data.affineNodes 80
    positiveArea_hlen (by norm_num)
    (by rw [Data.affineNodes_length]; norm_num) positiveArea_hlast,harea]
  have hq : (qPositiveArea Data.affineNodes 80 : ℝ) ≤
      (((16297236881532502 : ℚ)/(80*10000000000000000) : ℚ) : ℝ) := by
    exact_mod_cast actual_qPositiveArea
  rw [qPositiveArea_cast] at hq
  convert hq using 1 <;> norm_num

/-- Source-first actual exterior leakage provider. Original numerical inputs,
ceil-cell algorithm, and seven-output C host are preserved. -/
theorem source_first_positive_leak :
    IEANTN.CMSFunctional.positiveLeak (affineSpectrum Data.affineNodes 80) ≤
      (16297236881532502:ℝ)/(80*10000000000000000) :=
  source_output_positive_leak _ _ _ _ _ _ _ actual_source_scalar_output

#print axioms actual_qPositiveArea
#print axioms source_output_positive_leak
#print axioms source_first_positive_leak
end RH080Next.FapPV
