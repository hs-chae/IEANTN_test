/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Pair.QRHGeometry
import IEANTN.Nodes.FKS2Numerics.v7.Conclusions
import IEANTN.Nodes.FKS2.v6.Conclusions

namespace FKS2Pair.Updated
open Real IEANTN FKS2Table4

/-- Minimal adapter: identical conservative functional and original proved source theorem. -/
theorem verified_qrh_transport {out : ℚ}
    (he : ExecTransportAt selectedSource selected FKS2Table4.initial out) :
    Bsafe qProfile ≤ (out:ℝ)+(totalForwardError:ℝ) := by
  rw [qBsafe_eq]
  exact verified_fks2_transport (original_execution_of_at he)

theorem concrete_execution :
    ExecTransportAt selectedSource selected FKS2Table4.initial q :=
  original_execution_at FKS2Table4.concrete_execution

theorem selected_execution_witness : ∃ out : ℚ,
    ExecTransportAt selectedSource selected FKS2Table4.initial out ∧
    Bsafe qProfile ≤ (out:ℝ)+(totalForwardError:ℝ) :=
  ⟨q,concrete_execution,verified_qrh_transport concrete_execution⟩

theorem certified_allowance : Bsafe qProfile < (5:ℝ)/10^16 := by
  have hn : (q:ℝ)+(totalForwardError:ℝ)<(5:ℝ)/10^16 := by
    have h := (Rat.cast_lt (K := ℝ)).2 budget_checks.2.2.2.2.2.2.2.2.2
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using h
  exact (verified_qrh_transport concrete_execution).trans_lt hn

/-- Same generic whole-ray theorem as the frozen old application. -/
theorem numerical_pi (hpsi : QRHCH2.v5.psi_refined_bound)
    (hAnchor : FKS2.v6.table4_anchor_300) : FKS2Numerics.v7.qrh_pi := by
  intro x hx
  exact (FKS2Pair.whole_ray_transport (qProfile_valid hpsi) hAnchor x hx).trans
    certified_allowance.le
end FKS2Pair.Updated

theorem FKS2Numerics.v7.challenge_qrh_pi
    (hpsi : QRHCH2.v5.psi_refined_bound) (hAnchor : FKS2.v6.table4_anchor_300) :
    FKS2Numerics.v7.qrh_pi := FKS2Pair.Updated.numerical_pi hpsi hAnchor
