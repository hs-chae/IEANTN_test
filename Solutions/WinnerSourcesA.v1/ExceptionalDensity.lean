/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityTail
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic
namespace WinnerExceptionalDensity
open Real Set Filter Topology
set_option maxHeartbeats 0

/-- An actual finite zero count is monotone in its strict height cutoff.
Finite support and nonnegative analytic multiplicities are proved upstream. -/
theorem zetaN_mono (sigma : ℝ) : Monotone (IEANTN.zetaN' sigma) := by
  classical
  intro u v huv
  have hfin : (IEANTN.zetaZeroesIn (Ioo sigma 1) (Ioo 0 u)).Finite :=
    (CH2QRH.finite_zero_rectangle (Ioo sigma 1) (T:=u)).subset
      (fun z hz => ⟨hz.1,⟨hz.2.1.1,hz.2.1.2.le⟩,hz.2.2⟩)
  have hfin' : (IEANTN.zetaZeroesIn (Ioo sigma 1) (Ioo 0 v)).Finite :=
    (CH2QRH.finite_zero_rectangle (Ioo sigma 1) (T:=v)).subset
      (fun z hz => ⟨hz.1,⟨hz.2.1.1,hz.2.1.2.le⟩,hz.2.2⟩)
  rw [IEANTN.zetaN',IEANTN.zetaN',CH2QRH.rectangle_sum_eq hfin,CH2QRH.rectangle_sum_eq hfin']
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    rw [Set.Finite.mem_toFinset] at hz ⊢
    exact ⟨hz.1,⟨hz.2.1.1,hz.2.1.2.trans_le huv⟩,hz.2.2⟩
  · intro z hz _
    have hh := (Set.Finite.mem_toFinset hfin').mp hz
    exact mul_nonneg (by norm_num) (CH2Section7Z.zetaOrder_nonneg_of_mem
      Set.Ioo_subset_Ioi_self ⟨trivial,hh.2.1,hh.2.2⟩)

/-- No countable set covers a nonempty right interval. -/
theorem exists_right_not_mem {E : Set ℝ} (hE : E.Countable) (t e : ℝ) (he : 0<e) :
    ∃ u : ℝ, t<u ∧ u<t+e ∧ u∉E := by
  have hn : ¬Ioo t (t+e)⊆E := by
    intro hsub
    have hc := hE.mono hsub
    have hh := Cardinal.Real.Ioo_countable_iff.mp hc
    linarith
  obtain ⟨u,hu,hunot⟩ := Set.not_subset.mp hn
  exact ⟨u,hu.1,hu.2,hunot⟩

/-- Extend a newly proved continuous majorant from nonexceptional heights.
No continuity of the old raw moment expression is assumed or used. -/
theorem extend_countable_exceptional {N Q : ℝ→ℝ} {E : Set ℝ} {H T : ℝ}
    (hE : E.Countable) (hmono : MonotoneOn N (Ici H)) (hHT : H≤T)
    (hQ : ContinuousAt Q T)
    (hgood : ∀ u : ℝ, H≤u → u∉E → N u≤Q u) : N T≤Q T := by
  by_contra hbad
  have hlt : Q T<N T := lt_of_not_ge hbad
  have hevent : ∀ᶠ u in 𝓝 T, Q u<N T := hQ.eventually (gt_mem_nhds hlt)
  obtain ⟨e,he,hclose⟩ := Metric.eventually_nhds_iff.mp hevent
  obtain ⟨u,hu,hu',hunot⟩ := exists_right_not_mem hE T e he
  have hdist : dist u T<e := by
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hu)]
    linarith
  have hNu : N T≤N u := hmono hHT (hHT.trans hu.le) hu.le
  have hgoodu := hgood u (hHT.trans hu.le) hunot
  have hQu := hclose hdist
  linarith

/-- The actual zeta count requires no monotonicity hypothesis or source extension oracle. -/
theorem zetaN_extend {sigma H T : ℝ} {Q : ℝ→ℝ} {E : Set ℝ}
    (hE : E.Countable) (hHT : H≤T) (hQ : ContinuousAt Q T)
    (hgood : ∀ u : ℝ, H≤u → u∉E → IEANTN.zetaN' sigma u≤Q u) :
    IEANTN.zetaN' sigma T≤Q T :=
  extend_countable_exceptional hE ((zetaN_mono sigma).monotoneOn (Ici H)) hHT hQ hgood

#print axioms zetaN_mono
#print axioms extend_countable_exceptional
#print axioms zetaN_extend
end WinnerExceptionalDensity
