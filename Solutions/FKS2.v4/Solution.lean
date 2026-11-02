/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Correction.Audit300
import IEANTN.Nodes.FKS2.v4.Conclusions
open Real IEANTN

theorem FKS2.v4.challenge_baseline_theta
    (hF : FKS.v2.psi_classical_bound) (hB : BKLNW.v1.corollary_5_1)
    (hN : FKS2Numerics.v3.baseline_bound) : FKS2.v4.baseline_theta := by
  exact FKS2Correction.theta_from_application (by norm_num)
    (FKS2Correction.baseline_psi hF) hB hN

theorem FKS2.v4.challenge_baseline_intervals
    (hF : FKS.v2.psi_classical_bound) (hB : BKLNW.v1.corollary_5_1)
    (hN : FKS2Numerics.v3.baseline_bound) : FKS2.v4.baseline_intervals := by
  exact FKS2Correction.intervals_from_application
    (A := 121.096) (nubar := (11:ℝ)/10^62)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (FKS2Correction.baseline_psi hF) hB hN
