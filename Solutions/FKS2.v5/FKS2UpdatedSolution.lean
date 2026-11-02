/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Update.Result
import FKS2QRHAdapter
import IEANTN.Nodes.FKS2.v5.Conclusions
open Real IEANTN

theorem FKS2.v5.challenge_updated_theta
    (hP : QRHPropagation.v3.psi_classical_bound) (hB : BKLNW.v1.corollary_5_1)
    (hN : FKS2Numerics.v4.updated_bound) : FKS2.v5.updated_theta := by
  exact FKS2Correction.theta_from_application (by norm_num) hP hB hN

theorem FKS2.v5.challenge_updated_intervals
    (hP : QRHPropagation.v3.psi_classical_bound) (hB : BKLNW.v1.corollary_5_1)
    (hN : FKS2Numerics.v4.updated_bound) : FKS2.v5.updated_intervals := by
  exact FKS2Correction.intervals_from_application
    (A := 0.0000000001) (nubar := (2:ℝ)/10^49)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hP hB hN

theorem FKS2.v5.challenge_strict_improvement : FKS2.v5.strict_improvement := by
  norm_num [FKS2.v5.strict_improvement,FKS2.v5.Unew,FKS2.v4.Uold]
