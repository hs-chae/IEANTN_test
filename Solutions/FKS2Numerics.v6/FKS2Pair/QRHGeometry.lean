/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Pair.GenericSource
import FKS2Table4.Result

namespace FKS2Pair
open Real IEANTN FKS2Table4

noncomputable def qProfile (j : ℕ) : ℝ := Q (300+j)

theorem qProfile_valid (hpsi : QRHCH2.v5.psi_refined_bound) : ValidProfile qProfile := by
  constructor
  · intro j hj
    exact Q_nonneg _
  · intro j hj t ht
    exact theta_on_ray (theta_input hpsi)
      (by linarith [(Nat.cast_nonneg j : (0:ℝ)≤j)]) ht

theorem qCells_eq : cells qProfile = FKS2Table4.cells := by
  unfold cells FKS2Table4.cells
  apply Finset.sum_congr rfl
  intro j hj
  rw [← cell_normalization]
  unfold FKS2Table4.cell qProfile
  ring

theorem qBsafe_eq : Bsafe qProfile=FKS2Table4.allowance := by
  have h0 : qProfile 0=Q 300 := by simp [qProfile]
  have h30 : qProfile 30=Q 330 := by norm_num [qProfile]
  have ha : anchor qProfile=FKS2Table4.anchor := by simp [anchor,FKS2Table4.anchor,h0]
  simp only [Bsafe,FKS2Table4.allowance,ha,qCells_eq,h30]

theorem qr_literal_scale_check :
    loadLiteral selected.scale=some scale ∧ loadLiteral selected.anchor=some anchorUpper ∧
    loadLiteral selected.point=some pointUpper ∧ loadLiteral selected.tail=some tailUpper ∧
    additionCheck (qsum*scale) scaledOutput=true := by native_decide

theorem qr_suffix_IEEE : SuffixIEEE selected qsum q := by
  exact ⟨scale,anchorUpper,pointUpper,tailUpper,scaledOutput,anchorOutput,pointOutput,
    qr_literal_scale_check.1,qr_literal_scale_check.2.1,qr_literal_scale_check.2.2.1,
    qr_literal_scale_check.2.2.2.1,additionCheck_sound qr_literal_scale_check.2.2.2.2,
    additionCheck_sound suffix_checks.2.2.2.2.1,
    additionCheck_sound suffix_checks.2.2.2.2.2.1,
    additionCheck_sound suffix_checks.2.2.2.2.2.2.1⟩

theorem original_execution_at {out : ℚ} (h : FKS2Table4.ExecTransport selected out) :
    ExecTransportAt selectedSource selected FKS2Table4.initial out := by
  have hq := FKS2Table4.output_unique h
  subst out
  obtain ⟨hs,hp,xs,s,final,hl,hrep,hr,hkernel,hsuffix⟩ := h
  have hxs : xs=inputValues := Option.some.inj (hl.symm.trans execution_checks.1)
  subst xs
  have hsval : s=qsum := Option.some.inj (hr.symm.trans execution_checks.2.2.1)
  subst s
  exact ⟨hs,by decide,inputValues,qsum,final,hl,hrep,hr,hkernel,hsuffix,qr_suffix_IEEE⟩

theorem original_execution_of_at {out : ℚ}
    (h : ExecTransportAt selectedSource selected FKS2Table4.initial out) :
    FKS2Table4.ExecTransport selected out := by
  obtain ⟨hs,hn,xs,s,final,hl,hrep,hr,hkernel,hsuffix,hIEEE⟩ := h
  exact ⟨hs,rfl,xs,s,final,hl,hrep,hr,hkernel,hsuffix⟩
end FKS2Pair
