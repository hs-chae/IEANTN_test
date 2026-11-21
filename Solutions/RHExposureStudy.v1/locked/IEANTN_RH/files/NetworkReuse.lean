import FullRH
import RamanujanPV.CoupledLargeMargin

open Real IEANTN
namespace NetworkReuse

/-- Strict density throughout the FKS range is identically zero under full RH;
the coefficient table is not needed. This keeps the exact contract unchanged. -/
theorem fks_density_from_rh (hRH : SharedRH.hypothesis) : FKS.v3.density_0618 := by
  intro σ T hσ _ hT
  rw [FullRH.right_density_zero hRH σ T (by linarith)]
  have ht : 0 < T := by linarith [show (0:ℝ) < 3*10^12 by norm_num]
  have hlog : 0 < log T := log_pos (by linarith [show (1:ℝ) < 3*10^12 by norm_num])
  positivity

open RamanujanPV RamanujanPV.AnalyticTransition RamanujanPV.CoupledActualPi

section Inputs
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
    (hRH : SharedRH.hypothesis)
include hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH hRH

/-- Actual earlier proof of both pi sides, not merely the conclusion as a
predicate. Three old analytic/finite-height providers are replaced by RH. -/
theorem actual_pi_expansion : DudekPlattNumerics.v6.pi_two_sided_144 :=
  QRHFullTail.pi_two_sided_144 hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH
    (RH.LogicalAdapters.qrh hRH) (fks_density_from_rh hRH) (RH.LogicalAdapters.platt_trudgian hRH)

theorem actual_gap_six_trillion
    (hseries : LogIntegralSeriesIdentity IEANTN.li)
    (hoffset : RamanujanPV.Middle.LiOffsetIdentity)
    (hpositive : ButhePiBelowLi)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    (hCH2 : CH2.v1.corollary_1_3_psi)
    (hDusart : RamanujanPV.Middle.DusartPowerInput)
    (htheta : ButheThetaDeficit) (hlower : AxlerPiLower)
    (hupper : ButheThetaUpper)
    {x : ℝ} (hx : 1250000000000 ≤ x) : (6000000000000 : ℝ) < RamanujanPV.gap x :=
  CoupledLargeMargin.analytic_ray_gap_six_trillion hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH (RH.LogicalAdapters.qrh hRH) (fks_density_from_rh hRH)
    (RH.LogicalAdapters.platt_trudgian hRH)
    hseries hoffset hpositive hbuthe hCH2 hDusart htheta hlower hupper hx

end Inputs
#print axioms fks_density_from_rh
#print axioms actual_pi_expansion
#print axioms actual_gap_six_trillion
end NetworkReuse
