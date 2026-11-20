/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import RamanujanPhase2
import DensityCertificates
import RamanujanPV.QuantitativeTail

/-! Targeted fresh replay of the selected pi144 theorem. This imports the density
proof and its exact numerical certificates, not the eleven-consumer Phase2Replay.
The sixteen literature inputs are explicit and unchanged. -/
namespace RamanujanPV.QRHClosure
open Real IEANTN

theorem pi144
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
    RamanujanPV.Budget.PiInput 70 170 144 := by
  have hpsi := (CH2QRH.density_transfer_proved hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH) hFKS hRH hqrh
  constructor
  · intro x hx
    exact (QRHPhase2.pi_expansion_phase2 hpsi hx).1
  · intro x hx
    exact (QRHPhase2.pi_expansion_phase2 hpsi
      ((exp_le_exp.mpr (by norm_num : (144:ℝ) ≤ 144+1)).trans_lt hx)).2

#print axioms pi144
end RamanujanPV.QRHClosure
