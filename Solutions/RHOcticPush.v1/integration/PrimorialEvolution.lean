/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import NodeProviders
import ThetaRelay
import IEANTN.Nodes.Primorial.v3.Conclusions
namespace Primorial.v3
open Real IEANTN
/-- The actual node consumes the new typed psi output and the existing theta relay. -/
theorem challenge_box_growth (rh : RH.v1.hypothesis) (hb : Buthe2016.v1.theorem_2_psi)
    (hi : RHSmoothing.v2.box_psi) : box_growth := by
  intro n hn
  have hn0 : 0 < (n : ℝ) := (exp_pos 35).trans_le hn
  have hL : 35 ≤ log (n : ℝ) := by simpa using log_le_log (exp_pos 35) hn
  have hp := hi n hn
  have hp' : |Chebyshev.psi (exp (log (n : ℝ))) - exp (log (n : ℝ))| ≤
      RHOcticEvolution.boxBound (log (n : ℝ)) * sqrt (exp (log (n : ℝ))) := by
    simpa only [exp_log hn0, mul_comm] using hp
  have ht := RHContinuation.ThetaRelay.theta_relay rh hb
    (by linarith : 34 ≤ log (n : ℝ)) hp'
  simpa only [exp_log hn0, Chebyshev.theta_eq_log_primorial, Nat.floor_natCast,
    show (1.01 : ℝ) = 101 / 100 by norm_num] using ht
end Primorial.v3
#print axioms Primorial.v3.challenge_box_growth
