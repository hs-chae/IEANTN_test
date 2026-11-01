/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Applications
import IEANTN.Nodes.DudekPlattNumerics.v5.Conclusions

theorem DudekPlattNumerics.v5.challenge_pi_two_sided_qrh
    (hpsi : QRHCH2.v5.psi_refined_bound) : DudekPlattNumerics.v5.pi_two_sided_qrh :=
  fun _ hx ↦ QRHPropagation.pi_expansion hpsi hx
