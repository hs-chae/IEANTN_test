import SpectralRam606Cells
import RamStrongOverlay

/-! A different-input synthesis, preserving the accepted nine-input branch.
The local 606--610 billion bridge needs RH, Nicolas, general Perron and three
Büthe inputs. Its global overlay retains the old nine inputs and adds Nicolas
and Perron. No same-premise or published-onset-record claim is made.
-/
namespace RHOcticPush.SpectralRam
open Real Set IEANTN Ramanujan640 RHContinuation.Ramanujan
open RHOcticPush.Correlated RHOcticPush.BoxPerron
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable def frontier606 (x : ℝ) : ℝ :=
  if (610000000000 : ℝ) ≤ x then strongFrontier607 x else 1 / 1000

theorem actual_frontier606 (rh : SharedRH.hypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (606000000000 : ℝ) ≤ x) : frontier606 x ≤ RamStudy.RG x := by
  unfold frontier606
  split_ifs with h610
  · exact actual_strong_frontier607 rh hGM hP hJ hT1 hT2 hL hU hS (by linarith)
  · have hx0 : 0 < x := by linarith
    have h := bridge606 rh hN hI hT1 hL hU (z := log x)
      (by simpa only [exp_log hx0] using hx)
      (by rw [exp_log hx0]; linarith)
    simpa only [exp_log hx0] using h

theorem actual_margin606 (rh : SharedRH.hypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (606000000000 : ℝ) ≤ x) : (1 / 1000 : ℝ) ≤ RamStudy.RG x := by
  by_cases h610 : (610000000000 : ℝ) ≤ x
  · exact actual_ramanujan_610b_of_pair
      (fun _ _ _ hk0 hke hy hyx => GM.actual_pair_upper rh hGM hP hJ hk0 hke hy hyx)
      rh hGM hP hJ hT1 hT2 hL hU hS h610
  · have hx0 : 0 < x := by linarith
    have h := bridge606 rh hN hI hT1 hL hU (z := log x)
      (by simpa only [exp_log hx0] using hx)
      (by rw [exp_log hx0]; linarith)
    simpa only [exp_log hx0] using h

theorem preserves_strong_profile {x : ℝ} (hx : (610000000000 : ℝ) ≤ x) :
    frontier606 x = strongFrontier607 x := by simp [frontier606, hx]

theorem retains_full_original {x : ℝ} (hx : (640000000000 : ℝ) ≤ x) :
    frontier606 x = finalMargin x := by
  rw [preserves_strong_profile (by linarith)]
  exact retains_full_original_strong hx

theorem dominates_old_profile (x : ℝ) : strongFrontier607 x ≤ frontier606 x := by
  by_cases h610 : (610000000000 : ℝ) ≤ x
  · rw [preserves_strong_profile h610]
  · have h640 : ¬ (640000000000 : ℝ) ≤ x := by linarith
    have h620 : ¬ (620000000000 : ℝ) ≤ x := by linarith
    have h619 : ¬ (619000000000 : ℝ) ≤ x := by linarith
    norm_num [frontier606, strongFrontier607, frontier607, h610, h640, h620, h619]

theorem actual_gap606 (rh : SharedRH.hypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (606000000000 : ℝ) ≤ x) :
    (1 / 1000 : ℝ) * x^2 / (log x)^6 ≤ RamanujanGap.v1.gap x := by
  have hr := actual_margin606 rh hN hI hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6 / x^2 := by positivity
  have he : (log x^6 / x^2) * ((1 / 1000 : ℝ) * x^2 / (log x)^6) = 1 / 1000 := by
    field_simp [hx0.ne', hl.ne']
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

theorem actual_strict606 (rh : SharedRH.hypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (606000000000 : ℝ) ≤ x) :
    (primeCounting x)^2 < exp 1 * x / log x * primeCounting (x / exp 1) := by
  have h := actual_gap606 rh hN hI hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < (1 / 1000 : ℝ) * x^2 / (log x)^6 := by positivity
  unfold RamanujanGap.v1.gap at h
  linarith

#print axioms actual_frontier606
#print axioms actual_margin606
#print axioms preserves_strong_profile
#print axioms retains_full_original
#print axioms dominates_old_profile
#print axioms actual_gap606
#print axioms actual_strict606
end RHOcticPush.SpectralRam
