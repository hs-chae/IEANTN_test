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

/-- Exact input refinement at the seventh C output, including terminal zero. -/
theorem actual_maximum_coefficients : Data.affineNodes.all
    (fun a=>decide (|a|≤(6915614327570000:ℚ)/10000000000000000))=true := by decide +kernel

/-- The actual seventh output controls the actual supported spectrum. -/
theorem source_output_window_bound (f0 area height v0 v1 mu2 maximum : ℕ)
    (h : SourceScalarOutput f0 area height v0 v1 mu2 maximum) (v : ℝ) :
    |affineSpectrum Data.affineNodes 80 v|≤(maximum:ℝ)/10000000000000000 := by
  have hm : maximum=6915614327570000 :=
    (source_output_finite_specification _ _ _ _ _ _ _ h).2.2.2.2.2.2.trans
      Model.maximumNumerator_exact
  rw [hm]
  apply RH080Next.Primal.affineSpectrum_abs_le _ _ _
    (by rw [Data.affineNodes_length]; norm_num) (by norm_num)
  intro j hj
  have hall : ∀a∈Data.affineNodes,|a|≤(6915614327570000:ℚ)/10000000000000000 := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using actual_maximum_coefficients
  have hb:=node_abs_bound Data.affineNodes ((6915614327570000:ℚ)/10000000000000000)
    hall j (by omega)
  convert hb using 1 <;> norm_num

theorem source_first_window_bound (v : ℝ) :
    |affineSpectrum Data.affineNodes 80 v|≤(6915614327570000:ℝ)/10000000000000000 :=
  source_output_window_bound _ _ _ _ _ _ _ actual_source_scalar_output v

#print axioms actual_maximum_coefficients
#print axioms source_output_window_bound
#print axioms source_first_window_bound
end RH080Next.FapPV
