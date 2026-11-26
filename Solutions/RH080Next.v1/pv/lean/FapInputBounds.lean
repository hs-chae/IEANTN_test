/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScalarInputBounds
import FapSourceFinal
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RH080Next.FapPV
open RH080Next.Explicit RH080Next.ScalarInputBounds

/-- Exact mathematical input refinement, not a claim that C printed A0. -/
theorem actual_qMassA0 : qMassA0 Data.affineNodes 80 ≤2 := by decide +kernel

/-- Independent mathematical interpretation of the actual variation output. -/
theorem actual_qV0 : qV0 Data.affineNodes=
    (14047086942420000:ℚ)/10000000000000000 := by decide +kernel

/-- Exact input-only coefficient bound, including the appended terminal zero. -/
theorem actual_input_coefficients :
    Data.affineNodes.all (fun a => decide (|a|≤(1:ℚ)))=true := by decide +kernel

theorem input_mass_bound : nodalMassA0 Data.affineNodes 80≤2 := by
  have h : (qMassA0 Data.affineNodes 80 : ℝ)≤2 := by exact_mod_cast actual_qMassA0
  simpa only [qMassA0_cast] using h

theorem input_window_bound (v : ℝ) : |affineSpectrum Data.affineNodes 80 v|≤1 := by
  apply RH080Next.Primal.affineSpectrum_abs_le _ _ _
    (by rw [Data.affineNodes_length]; norm_num) (by norm_num)
  intro j hj
  have hall : ∀a∈Data.affineNodes,|a|≤(1:ℚ) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using actual_input_coefficients
  simpa only [Rat.cast_one] using node_abs_bound _ _ hall j (by omega)

theorem source_output_variation (f0 area height v0 v1 mu2 maximum : ℕ)
    (h : SourceScalarOutput f0 area height v0 v1 mu2 maximum) :
    nodalV0 Data.affineNodes=(v0:ℝ)/10000000000000000 := by
  have hv0 : v0=14047086942420000 :=
    (source_output_finite_specification _ _ _ _ _ _ _ h).2.2.2.1.trans
      Model.firstVariationNumerator_exact
  rw [hv0,←qV0_cast,actual_qV0]
  norm_num

theorem source_first_variation :
    nodalV0 Data.affineNodes=(14047086942420000:ℝ)/10000000000000000 :=
  source_output_variation _ _ _ _ _ _ _ actual_source_scalar_output

#print axioms actual_qMassA0
#print axioms actual_qV0
#print axioms actual_input_coefficients
#print axioms input_mass_bound
#print axioms input_window_bound
#print axioms source_output_variation
#print axioms source_first_variation
end RH080Next.FapPV
