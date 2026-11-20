/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.EarlyMiddle
import RamanujanPV.QRHFullTail

/-!
# Actual Ramanujan analytic ray with the original QRH inputs

The two-sided prime-count expansion is DERIVED here, not assumed as an
additional external premise. The finite certificate in the last theorem is a
remaining exact source/count/enclosure obligation; this file does not assert
that the full numerical certificate has been formally constructed.
-/
namespace RamanujanPV.FinalAnalytic
open Real IEANTN RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0

section OriginalInputs
variable
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper) (h24l : CH2.v2.proposition_2_4_lower)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (hFKS : FKS.v3.density_0618) (hRH : PlattTrudgian.v1.rh_up_to)
    (hseries : LogIntegralSeriesIdentity IEANTN.li)
    (hoffset : Middle.LiOffsetIdentity)
    (hpositive : ButhePiBelowLi)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    (hCH2 : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤
      Real.pi / (3 * (10 : ℝ)^12) * t + (113.67 : ℝ) * sqrt t)
    (hDusart : Middle.DusartPowerInput)

include hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH hqrh hFKS hRH
  hseries hoffset hpositive hbuthe hCH2 hDusart

/-- The reported quantitative margin, now on the entire closed height40 ray,
with the sixteen QRH/density inputs supplied to their actual existing proof. -/
theorem quantitative_from40 {x : ℝ} (hx40 : exp 40 ≤ x) :
    (37 / 200 : ℝ) * x ^ 2 / log x ^ 6 < RamanujanPV.gap x := by
  have hpi144 := QRHFullTail.pi_two_sided_144 hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hqrh hFKS hRH
  have hli2 : 0 ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2 :=
    ⟨(primeCounting_nonneg 2).trans (hpositive 2 (by norm_num)).le, li_two_upper hseries⟩
  have hlog2 : (2 / 3 : ℝ) ≤ log 2 := by linarith [log_two_decimal.1]
  have hDeficit : FiniteMiddle.ButheDeficit19 := by
    intro t ht htU
    exact hbuthe t ⟨ht, htU⟩
  have hBelow : FiniteMiddle.ButheBelow19 := by
    intro t ht htU
    exact (hpositive t ⟨ht, htU⟩).le
  exact EarlyMiddle.actual_gap_from40_pending_QRH_adapter hx40 hCH2 hDusart
    hDeficit hBelow hoffset hli2 hlog2 hpi144

variable (htheta : ButheThetaDeficit) (hlower : AxlerPiLower)
include htheta hlower

/-- All real inputs beyond the improved analytic transition. No finite
Ramanujan inequality, numerical table or additional pi144 premise is assumed. -/
theorem analytic_ray {x : ℝ} (hx : (1490000000000 : ℝ) ≤ x) : Holds x := by
  by_cases h19 : x ≤ (10000000000000000000 : ℝ)
  · exact actual_ramanujan_analytic_bridge hseries hoffset hpositive htheta hlower hbuthe
      ⟨hx, h19⟩
  · have hx40 : exp (40 : ℝ) ≤ x :=
      (exp_le_exp.mpr (by norm_num : (40 : ℝ) ≤ 43)).trans
        (exp43_le_1e19.trans (le_of_not_ge h19))
    have hg := quantitative_from40 hfe hdig h24u h24l hk hneg h2v hv hcs
      hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart hx40
    have hx0 : 0 < x := (exp_pos 40).trans_le hx40
    have hL : (40 : ℝ) ≤ log x := by simpa using log_le_log (exp_pos 40) hx40
    apply (holds_iff_gap_pos x).2
    exact (show (0 : ℝ) < (37 / 200 : ℝ) * x ^ 2 / log x ^ 6 by positivity).trans hg

/-- The remaining finite proof plugs directly into the finished analytic ray.
The certificate contains actual prime counts, exact arithmetic, real enclosures
and full adjacency; its existence has NOT been proved for the full prefix. -/
theorem all_real_from_completed_finite_certificate {cs : List Cell}
    (certificate : CompleteCertificate 38358837683 1490000000001 cs) :
    ∀ x : ℝ, 38358837683 ≤ x →
      primeCounting x ^ 2 < exp 1 * x / log x * primeCounting (x / exp 1) := by
  intro x hx
  by_cases hfinite : x < (1490000000001 : ℝ)
  · exact complete_certificate_sound certificate x (by exact_mod_cast hx) hfinite
  · have hxA : (1490000000000 : ℝ) ≤ x := by linarith [le_of_not_gt hfinite]
    exact analytic_ray hfe hdig h24u h24l hk hneg h2v hv hcs
      hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart
      htheta hlower hxA

end OriginalInputs

#check @quantitative_from40
#check @analytic_ray
#check @all_real_from_completed_finite_certificate
#print axioms quantitative_from40
#print axioms analytic_ray
#print axioms all_real_from_completed_finite_certificate
end RamanujanPV.FinalAnalytic
