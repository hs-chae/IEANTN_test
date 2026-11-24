import BoxFirstMoment
import BoxHDerivative
import BoxLaurentProduct
import StieltjesConstant

/-! The exact original logarithmic Box moment, with all analytic inputs proved. -/
namespace RHOcticPush.BoxGamma
open Real Filter Set RHOcticPush.StieltjesZeta
open scoped Topology

lemma zetaSeries_regularized {s : ℝ} (hs : 0 < s) :
    zetaSeries s = 1/s + regularizedZeta s := by
  have hn : 1 + (s : ℂ) ≠ 1 := by
    intro he
    have h := congrArg Complex.re he
    norm_num at h
    linarith
  have hc : ((1+s : ℝ) : ℂ) = 1 + (s : ℂ) := by push_cast; ring
  have hz := congrArg Complex.re (zetaSeries_eq hs)
  rw [hc, riemannZeta_eq_inv_sub_add hn] at hz
  simpa [regularizedZeta] using hz

theorem actual_box_linear_coefficient :
    Tendsto (fun s : ℝ => (BoxMellin.mellin s - 1/s - Real.log 2)/s)
      (𝓝[>] 0)
      (𝓝 (-BoxMellinInputs.v1.gamma1 - BoxMellinInputs.v1.q +
        BoxMellinInputs.v1.a * Real.log 2 - BoxMellinInputs.v1.a^2 / 2 +
        1/2 + Real.pi^2 / 24)) := by
  have ht := prefactor_laurent_product regularizedZeta_hasDerivAt hSeries_hasDerivAt
  rw [regularizedZeta_zero, hSeries_zero] at ht
  have hc : 1 - Real.eulerMascheroniConstant - Real.log 2 +
      Real.eulerMascheroniConstant + (2 * Real.log 2 - 1) = Real.log 2 := by ring
  have hd : ((1 - Real.eulerMascheroniConstant - Real.log 2)^2 + 1 + Real.pi^2 / 12) / 2 +
      (1 - Real.eulerMascheroniConstant - Real.log 2) *
        (Real.eulerMascheroniConstant + (2 * Real.log 2 - 1)) +
        (-BoxMellinInputs.v1.gamma1) + (-BoxMellinInputs.v1.q) =
      -BoxMellinInputs.v1.gamma1 - BoxMellinInputs.v1.q +
        BoxMellinInputs.v1.a * Real.log 2 - BoxMellinInputs.v1.a^2 / 2 +
        1/2 + Real.pi^2 / 24 := by unfold BoxMellinInputs.v1.a; ring
  rw [hc, hd] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  rw [actual_box_factorization hs.1 hs.2, zetaSeries_regularized hs.1]

/-- The canonical moment involves the original integral, q and Stieltjes limit. -/
theorem actual_box_J1 : IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 1 =
    -BoxMellinInputs.v1.gamma1 - BoxMellinInputs.v1.q +
      BoxMellinInputs.v1.a * Real.log 2 - BoxMellinInputs.v1.a^2 / 2 +
      1/2 + Real.pi^2 / 24 := by
  have ht := BoxMellin.linear_coefficient_tendsto
  rw [actual_box_J0] at ht
  exact tendsto_nhds_unique ht actual_box_linear_coefficient

/-- The full original predicate, including actual integrability, without parameters. -/
theorem second_moment_identity : BoxMellinInputs.v1.second_moment_identity :=
  Box.second_moment_iff.mpr actual_box_J1

#print axioms zetaSeries_regularized
#print axioms actual_box_linear_coefficient
#print axioms actual_box_J1
#print axioms second_moment_identity
end RHOcticPush.BoxGamma
