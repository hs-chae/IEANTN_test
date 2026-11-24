import SpectralRamProfile
import SpectralRamFrontier
import RamanujanEvolution
import SpectralNetwork
import IEANTN.Nodes.RamanujanGap.v6.Conclusions

namespace RamanujanGap.v6
open Real IEANTN
set_option maxHeartbeats 0

theorem challenge_local_606b (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi) :
    local_606b := by
  intro x hx hu
  exact RHOcticPush.SpectralRam.local_actual_gap hE hTab hL hU hx hu

theorem challenge_full_profile (localGap : local_606b) (old : RamanujanGap.v5.full_profile) :
    full_profile := by
  intro x hx
  by_cases h610 : (610000000000 : ℝ) ≤ x
  · simpa only [profile, if_pos h610] using old x (by linarith : 607000000000 ≤ x)
  · simpa only [profile, if_neg h610] using localGap x hx (by linarith : x ≤ 610000000000)

lemma profile_floor {x : ℝ} (hx : (606000000000 : ℝ) ≤ x) :
    (1 / 1000 : ℝ) ≤ profile x := by
  have hl : 0 < log x := log_pos (by linarith : 1 < x)
  by_cases h610 : (610000000000 : ℝ) ≤ x
  · simp only [profile, if_pos h610]
    by_cases h640 : (640000000000 : ℝ) ≤ x
    · simp only [RamanujanGap.v5.profile, if_pos h640]
      unfold RamanujanGap.v3.profile
      by_cases h70 : exp 70 ≤ x
      · rw [if_pos h70]
        apply le_trans (b := 1 + 14 / log x + 144 / (log x)^2) _ (le_max_left _ _)
        have h1 : 0 ≤ 14 / log x := by positivity
        have h2 : 0 ≤ 144 / (log x)^2 := by positivity
        linarith
      · rw [if_neg h70]
        by_cases h42 : exp 42 ≤ x
        · rw [if_pos h42]
          exact (by norm_num : (1 / 1000 : ℝ) ≤ 4 / 5).trans (le_max_left _ _)
        · rw [if_neg h42]
          norm_num
    · simp only [RamanujanGap.v5.profile, if_neg h640]
      by_cases h620 : (620000000000 : ℝ) ≤ x
      · rw [if_pos h620]
        norm_num
      · rw [if_neg h620]
        by_cases h619 : (619000000000 : ℝ) ≤ x
        · rw [if_pos h619]
          norm_num
        · simp only [if_neg h619, if_pos h610, le_refl]
  · simp only [profile, if_neg h610, le_refl]

theorem challenge_margin_606b (full : full_profile) : margin_606b := by
  intro x hx
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (profile_floor hx) (sq_nonneg x))
    (by positivity : 0 ≤ (log x)^6)
  exact h.trans (full x hx)

theorem challenge_ramanujan (margin : margin_606b) : ramanujan := by
  intro x hx
  have h := margin x hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith : 1 < x)
  have hp : 0 < (1 / 1000 : ℝ) * x^2 / (log x)^6 := by positivity
  unfold RamanujanGap.v1.gap at h
  linarith

theorem challenge_retains_v5_profile : retains_v5_profile := by
  intro x hx
  simp only [profile, if_pos hx]

theorem challenge_retains_original_margin (retains : retains_v5_profile)
    (old : RamanujanGap.v5.retains_original_margin) : retains_original_margin := by
  intro x hx
  exact (retains x (by linarith : 610000000000 ≤ x)).trans (old x hx)

theorem challenge_profile_gain : profile_gain := by
  constructor
  · intro x hx
    by_cases h610 : (610000000000 : ℝ) ≤ x
    · simp only [profile, if_pos h610, le_refl]
    · have h640 : ¬ (640000000000 : ℝ) ≤ x := by linarith
      have h620 : ¬ (620000000000 : ℝ) ≤ x := by linarith
      have h619 : ¬ (619000000000 : ℝ) ≤ x := by linarith
      norm_num [profile, RamanujanGap.v5.profile, h610, h640, h620, h619]
  · intro x hx hlt
    have h610 : ¬ (610000000000 : ℝ) ≤ x := not_le.mpr hlt
    have h640 : ¬ (640000000000 : ℝ) ≤ x := by linarith
    have h620 : ¬ (620000000000 : ℝ) ≤ x := by linarith
    have h619 : ¬ (619000000000 : ℝ) ≤ x := by linarith
    norm_num [profile, RamanujanGap.v5.profile, h610, h640, h620, h619]
end RamanujanGap.v6

namespace RHOcticPush.Network
open Real IEANTN
set_option maxHeartbeats 0
/-- Actual typed signed-profile to Ramanujan synthesis. Its11-source package
is explicit and distinct from the unchanged nine-input607b branch. -/
theorem fully_derived_spectral_ramanujan
    (rh : RH.v1.hypothesis) (hi : IntegratedPerron.v1.formula)
    (hn : Nicolas.v1.spectral_bound) (hg : RHPrimeCounting.v1.gm_source)
    (hp : Buthe.v1.theorem_2_psi) (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (h1 : Buthe.v1.table_1_interval_bounds) (h2 : Buthe.v1.table_2_interval_bounds)
    (hl : Buthe.v1.theorem_2_li_minus_pi) (hu : Buthe.v1.theorem_2_li_gt_pi)
    (hs : Buthe2016.v1.theorem_2_li_minus_pi) :
    RamanujanGap.v6.local_606b ∧ RamanujanGap.v6.full_profile ∧
    RamanujanGap.v6.margin_606b ∧ RamanujanGap.v6.ramanujan ∧
    RamanujanGap.v6.retains_v5_profile ∧ RamanujanGap.v6.retains_original_margin ∧
    RamanujanGap.v6.profile_gain := by
  have spectral := RHPrimeCounting.v5.challenge_compensation_profile rh hi hn
  have transfer := RHPrimeCounting.v3.challenge_refined_transfer rh hg hp hj
  have pair := RHPrimeCounting.v3.challenge_paired_transfer rh hg transfer
  have old := RamanujanGap.v5.challenge_full_profile pair rh hg hp hj h1 h2 hl hu hs
  have localGap := RamanujanGap.v6.challenge_local_606b spectral h1 hl hu
  have full := RamanujanGap.v6.challenge_full_profile localGap old
  have margin := RamanujanGap.v6.challenge_margin_606b full
  have retains := RamanujanGap.v6.challenge_retains_v5_profile
  exact ⟨localGap, full, margin, RamanujanGap.v6.challenge_ramanujan margin, retains,
    RamanujanGap.v6.challenge_retains_original_margin retains
      RamanujanGap.v5.challenge_retains_original_margin,
    RamanujanGap.v6.challenge_profile_gain⟩
end RHOcticPush.Network
#print axioms RamanujanGap.v6.challenge_local_606b
#print axioms RamanujanGap.v6.challenge_full_profile
#print axioms RamanujanGap.v6.challenge_margin_606b
#print axioms RamanujanGap.v6.challenge_ramanujan
#print axioms RamanujanGap.v6.challenge_retains_v5_profile
#print axioms RamanujanGap.v6.challenge_retains_original_margin
#print axioms RamanujanGap.v6.challenge_profile_gain
#print axioms RHOcticPush.Network.fully_derived_spectral_ramanujan
