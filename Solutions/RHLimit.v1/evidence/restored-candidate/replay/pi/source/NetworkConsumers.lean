/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHSmoothingInputs.v1.Conclusions
import IEANTN.Nodes.RHSmoothing.v1.Conclusions
import IEANTN.Nodes.PrimeKernelInputs.v1.Conclusions
import IEANTN.Nodes.PrimeInterval.v2.Conclusions
import IEANTN.Nodes.PrimeQuantile.v1.Conclusions
import IEANTN.Nodes.Lcm.v4.Conclusions
import IEANTN.Nodes.Primorial.v2.Conclusions
import IEANTN.Nodes.RH.v1.Conclusions
import PsiClosedElementary
import OcticConsumer
import OcticCubes
import RecoveredPNTClosed
import ThetaRelay
namespace RHContinuation.Network
open Real IEANTN

theorem box_psi (rh : RH.v1.hypothesis)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hm : RHSmoothingInputs.v1.box_moments) : RHSmoothing.v1.box_psi :=
  RHContinuation.Parabolic.psi_fast rh hef hz hm.1 hm.2

theorem B5_psi (rh : RH.v1.hypothesis)
    (hi : RHSmoothingInputs.v1.parabola_inputs) : RHSmoothing.v1.B5_psi :=
  RHContinuation.Parabolic.psi_B5 rh hi.1 hi.2.1 hi.2.2.1 hi.2.2.2

theorem box_improves_B5 : RHSmoothing.v1.box_improves_B5 :=
  fun _ hL => PsiBoxExact.fast_improves_B5 hL

theorem recovered_ch_psi (rh : RH.v1.hypothesis)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hn : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2 : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hc : CotangentSeries.v1.cot_series_zeta_values)
    (hr : ZeroCount.v1.rvm_error_bound) (hs : ZeroCount.v1.rvm_error_small)
    (hh : ZetaHadamard.v1.logDeriv_partial_fractions) : RHSmoothing.v1.recovered_ch_psi := by
  intro x hx
  have hx0 : 0 < x := (exp_pos 34).trans_le hx
  have hL : 34 ≤ log x := by simpa using log_le_log (exp_pos 34) hx
  have h := PNTStudy.sharpened_recovered rh hk hn h2 hv hc hr hs hh hL
  have hcoef : PNTStudy.coeffA (log x) + 0.181 = RHSmoothing.chBound (log x) := by
    norm_num [PNTStudy.coeffA, RHSmoothing.chBound]
  rw [hcoef, exp_log hx0] at h
  exact h

theorem count_215 (rh : RH.v1.hypothesis)
    (hi : PrimeKernelInputs.v1.octic_215) : PrimeInterval.v2.count_215 :=
  OcticConsumer.prime_count_215 rh hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1
    hi.2.2.2.2.1 hi.2.2.2.2.2

theorem count_family (rh : RH.v1.hypothesis)
    (hi : PrimeKernelInputs.v1.octic_family) : PrimeInterval.v2.count_family :=
  OcticConsumer.prime_count_family rh
    (fun C hC => (hi C hC).1) (fun C hC => (hi C hC).2.1)
    (fun C hC => (hi C hC).2.2.1) (fun C hC => (hi C hC).2.2.2.1)
    (fun C hC => (hi C hC).2.2.2.2.1) (fun C hC => (hi C hC).2.2.2.2.2)

theorem octic_block (hi : PrimeInterval.v2.count_215) : PrimeQuantile.v1.octic_block :=
  fun _ hu _ hm => RHContinuation.PrimeQuantiles.octic_quantiles hi hu hm

theorem successive_cubes (hi : PrimeInterval.v2.count_215) : PrimeQuantile.v1.successive_cubes :=
  RHContinuation.OcticCubes.prime_between_cubes hi

theorem box_lcm (hi : RHSmoothing.v1.box_psi) : Lcm.v4.box_growth := by
  intro n hn
  simpa only [Chebyshev.psi_eq_log_lcmUpto] using hi n hn

theorem recovered_lcm (hi : RHSmoothing.v1.recovered_ch_psi) : Lcm.v4.recovered_growth := by
  intro n hn
  simpa only [Chebyshev.psi_eq_log_lcmUpto] using hi n hn

theorem box_primorial (rh : RH.v1.hypothesis) (hb : Buthe2016.v1.theorem_2_psi)
    (hi : RHSmoothing.v1.box_psi) : Primorial.v2.box_growth := by
  intro n hn
  have hn0 : 0 < (n : ℝ) := (exp_pos 35).trans_le hn
  have hL : 35 ≤ log (n : ℝ) := by simpa using log_le_log (exp_pos 35) hn
  have hp := hi n hn
  have hp' : |Chebyshev.psi (exp (log (n : ℝ))) - exp (log (n : ℝ))| ≤
      RHSmoothing.fastBound (log (n : ℝ)) * sqrt (exp (log (n : ℝ))) := by
    simpa only [exp_log hn0, mul_comm] using hp
  have ht := RHContinuation.ThetaRelay.theta_relay rh hb (by linarith : 34 ≤ log (n : ℝ)) hp'
  simpa only [exp_log hn0, Chebyshev.theta_eq_log_primorial, Nat.floor_natCast, show (1.01 : ℝ) = 101 / 100 by norm_num] using ht

#print axioms box_psi
#print axioms B5_psi
#print axioms box_improves_B5
#print axioms recovered_ch_psi
#print axioms count_215
#print axioms count_family
#print axioms octic_block
#print axioms successive_cubes
#print axioms box_lcm
#print axioms recovered_lcm
#print axioms box_primorial
#print box_psi
#print recovered_ch_psi
#print count_215
#print box_primorial
end RHContinuation.Network
