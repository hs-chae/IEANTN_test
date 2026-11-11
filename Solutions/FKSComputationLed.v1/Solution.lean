/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.CoverSound
import IEANTN.Nodes.FKSComputationLed.v1.Conclusions
open Real IEANTN

theorem FKSComputationLed.v1.challenge_finite_pi_li :
    FKSComputationLed.v1.finite_pi_li := FKSComputationLed.CoverSound.finite_pnt

theorem FKSComputationLed.v1.challenge_finite_relative_error
    (h : FKSComputationLed.v1.finite_pi_li) :
    FKSComputationLed.v1.finite_relative_error := by
  intro x hx hxU
  have hx0 : 0<x := by linarith
  have hlog : 0<log x := log_pos (by linarith)
  have hs : 0<sqrt x := sqrt_pos.mpr hx0
  have hh := (div_le_div_of_nonneg_right (h x hx hxU) (div_nonneg hx0.le hlog.le))
  unfold Eπ
  calc
    _ ≤ ((19/10:ℝ)*sqrt x/log x)/(x/log x) := hh
    _ = _ := by field_simp; nlinarith [sq_sqrt hx0.le]

#print axioms FKSComputationLed.v1.challenge_finite_pi_li
#print axioms FKSComputationLed.v1.challenge_finite_relative_error
