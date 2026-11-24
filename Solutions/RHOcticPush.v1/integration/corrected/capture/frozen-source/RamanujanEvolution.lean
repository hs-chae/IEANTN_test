/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import NodeProviders
import RamStrongOverlay
import OldRamFullSolution
import IEANTN.Nodes.RamanujanGap.v5.Conclusions
namespace RamanujanGap.v5
open Real IEANTN RHContinuation.Ramanujan RHOcticPush.Correlated
set_option maxHeartbeats 0
lemma profile_eq_strong (x : ℝ) : profile x=strongFrontier607 x := by
  unfold profile strongFrontier607 frontier607
  split_ifs <;> first | exact RamanujanGap.v3.profile_eq x | rfl

theorem challenge_margin_607b (paired : RHPrimeCounting.v3.paired_transfer) (rh : RH.v1.hypothesis)
    (hg : RHPrimeCounting.v1.gm_source) (hp : Buthe.v1.theorem_2_psi)
    (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (h1 : Buthe.v1.table_1_interval_bounds) (h2 : Buthe.v1.table_2_interval_bounds)
    (hl : Buthe.v1.theorem_2_li_minus_pi) (hu : Buthe.v1.theorem_2_li_gt_pi)
    (hs : Buthe2016.v1.theorem_2_li_minus_pi) : margin_607b := by
  intro x hx
  apply RamanujanGap.v3.normalized_to_gap (by linarith : 1<x)
  exact actual_ramanujan_607b_of_pair paired rh hg hp hj h1 h2 hl hu hs hx

theorem challenge_full_profile (paired : RHPrimeCounting.v3.paired_transfer) (rh : RH.v1.hypothesis)
    (hg : RHPrimeCounting.v1.gm_source) (hp : Buthe.v1.theorem_2_psi)
    (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (h1 : Buthe.v1.table_1_interval_bounds) (h2 : Buthe.v1.table_2_interval_bounds)
    (hl : Buthe.v1.theorem_2_li_minus_pi) (hu : Buthe.v1.theorem_2_li_gt_pi)
    (hs : Buthe2016.v1.theorem_2_li_minus_pi) : full_profile := by
  intro x hx
  rw [profile_eq_strong]
  exact actual_strong_frontier_gap607_of_pair paired rh hg hp hj h1 h2 hl hu hs hx

theorem challenge_ramanujan (h : margin_607b) : ramanujan := by
  intro x hx
  have hb := h x hx
  have hx0 : 0<x := by linarith
  have hl : 0<log x := log_pos (by linarith : 1<x)
  have hpos : 0<(1/10000:ℝ)*x^2/(log x)^6 := by positivity
  unfold RamanujanGap.v1.gap at hb
  linarith

theorem challenge_retains_original_margin : retains_original_margin := by
  intro x hx
  simp only [profile,if_pos hx]

theorem challenge_profile_gain : profile_gain := by
  constructor
  · intro x hx
    by_cases h640 : (640000000000:ℝ)≤x
    · simp only [profile,RamanujanGap.v4.profile,if_pos h640,le_refl]
    · simp only [profile,RamanujanGap.v4.profile,if_neg h640,if_pos hx]
      norm_num
  · intro x hx h640
    have hn : ¬(640000000000:ℝ)≤x := not_le.mpr h640
    simp only [profile,RamanujanGap.v4.profile,if_neg hn,if_pos hx]
    norm_num
end RamanujanGap.v5
#print axioms RamanujanGap.v5.challenge_margin_607b
#print axioms RamanujanGap.v5.challenge_full_profile
#print axioms RamanujanGap.v5.challenge_ramanujan
#print axioms RamanujanGap.v5.challenge_profile_gain
