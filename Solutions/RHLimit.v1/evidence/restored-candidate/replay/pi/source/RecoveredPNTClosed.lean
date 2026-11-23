import RecoveredPNT
import ClosedCH2Compat
import GammaStrip
import ClosedZeta

open Real IEANTN
namespace PNTStudy

/-- Consume four additional exact existing proofs, preserving only the
eight explicitly named analytic contracts and RH as external inputs. -/
theorem sharpened_recovered
    (hRH : SharedRH.hypothesis)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {L : ℝ} (hL : 34 ≤ L) :
    |Chebyshev.psi (exp L) - exp L| ≤ (coeffA L + 0.181) * sqrt (exp L) :=
  no_ordinate_sum_recovered hRH ZetaLogDeriv.v1.challenge_logDeriv_functional_equation
    GammaSolution.digamma_sub_log_strip
    CH2.v2.challenge_proposition_2_4_upper CH2.v2.challenge_proposition_2_4_lower
    hk hneg h2v hv hcs hrvm hsmall hH hL

#print axioms sharpened_recovered
end PNTStudy
