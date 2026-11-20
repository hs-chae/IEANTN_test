/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import RamanujanPV.QRHClosure

/-! Exact v6 consumer adapter. Unlike the deliberately weaker generic Budget
contract, this retains BOTH inequalities on x>exp144. The sixteen original
inputs and the existing density/prime-count proof are unchanged. -/
namespace RamanujanPV.QRHFullTail
open Real IEANTN

theorem pi_two_sided_144
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
    (hFKS : FKS.v3.density_0618) (hRH : PlattTrudgian.v1.rh_up_to) :
    DudekPlattNumerics.v6.pi_two_sided_144 := by
  have hpsi := (CH2QRH.density_transfer_proved hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH) hFKS hRH hqrh
  intro x hx
  exact QRHPhase2.pi_expansion_phase2 hpsi hx

#check @pi_two_sided_144
#print axioms pi_two_sided_144
end RamanujanPV.QRHFullTail
