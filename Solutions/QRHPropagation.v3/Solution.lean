/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2QRHAdapter

theorem QRHPropagation.v3.challenge_psi_classical_bound
    (hpsi : QRHCH2.v5.psi_refined_bound) : QRHPropagation.v3.psi_classical_bound := by
  exact FKS2QRHAdapter.psi_same_shape hpsi
