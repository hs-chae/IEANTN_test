import GMTransport

/-! Preserve the entire old function by taking a proved minimum. Strict gain
below is on the stated common ray, not on the new provider's earliest domain. -/
namespace RHOcticPush.GM
open Real Set IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0

lemma ratio_derivative {L : ℝ} (hL : 0 < L) :
    HasDerivAt (fun t : ℝ => exp (t / 2) / t ^ 3)
      (exp (L / 2) * (L - 6) / (2 * L ^ 4)) L := by
  have hd := (((hasDerivAt_id L).div_const (2 : ℝ)).exp).div
    ((hasDerivAt_id L).pow 3) (pow_ne_zero 3 hL.ne')
  convert! hd using 1
  norm_num [Pi.div_apply, Pi.pow_apply, id_eq]
  field_simp [hL.ne']
  ring

lemma ratio_mono : MonotoneOn (fun L : ℝ => exp (L / 2) / L ^ 3) (Ici 24) := by
  have hd {L : ℝ} (hL : (24 : ℝ) ≤ L) := ratio_derivative (by linarith : 0 < L)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro L hL
    exact (hd hL).continuousAt.continuousWithinAt
  · intro L hL
    exact (hd (interior_subset hL)).differentiableAt.differentiableWithinAt
  · intro L hL
    have h24 : (24 : ℝ) ≤ L := interior_subset hL
    rw [(hd h24).deriv]
    have h6 : 0 < L - 6 := by linarith
    have h0 : 0 < L := by linarith
    positivity

lemma gain_at_anchor : (157 / 100 : ℝ) < (693 / 5000 : ℝ) * exp 12 / 24 ^ 3 := by
  interval_decide 80 (trust := kernel) <;> ring

lemma strict_gain_log {L : ℝ} (hL : 24 ≤ L) :
    (1 / 2 : ℝ) < RHLimit.Spectral.refinedBound (exp L) -
      ((1551 / 100 : ℝ) + leading 5 (exp L)) := by
  have h0 : 0 < L := by linarith
  have h5 : 0 < L - 5 := by linarith
  have h6 : 0 < L - 6 := by linarith
  have hm := ratio_mono (show (24 : ℝ) ∈ Ici (24 : ℝ) by simp)
    (show L ∈ Ici (24 : ℝ) from hL) hL
  have hb : (157 / 100 : ℝ) < (693 / 5000 : ℝ) * exp (L / 2) / L ^ 3 := by
    have ha := gain_at_anchor
    norm_num only [show (24 : ℝ) / 2 = 12 by norm_num] at hm
    have hm' : (693 / 5000 : ℝ) * exp 12 / 24 ^ 3 ≤
        (693 / 5000 : ℝ) * exp (L / 2) / L ^ 3 := by
      convert! mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 693 / 5000)
        using 1 <;> norm_num <;> (try ring)
    exact ha.trans_le hm'
  have hd : L * (L - 6) * (L - 5) ≤ L ^ 3 := by nlinarith
  have hq : (693 / 5000 : ℝ) * exp (L / 2) / L ^ 3 ≤
      (693 / 5000 : ℝ) * exp (L / 2) / (L * (L - 6) * (L - 5)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hd
  have he : RHLimit.Spectral.refinedBound (exp L) -
      ((1551 / 100 : ℝ) + leading 5 (exp L)) =
      (693 / 5000 : ℝ) * exp (L / 2) / (L * (L - 6) * (L - 5)) - 107 / 100 := by
    unfold RHLimit.Spectral.refinedBound RHLimit.Spectral.refinedLeading leading
    rw [Real.log_exp, ← Real.exp_half]
    field_simp [h0.ne', h5.ne', h6.ne'] <;> ring
  rw [he]
  linarith

noncomputable def evolvedBound (x : ℝ) : ℝ :=
  if exp 15 ≤ x then min (RHLimit.Spectral.refinedBound x)
    ((1551 / 100 : ℝ) + leading 5 x) else RHLimit.Spectral.refinedBound x

theorem actual_J_evolved (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {x : ℝ} (hx : exp 12 ≤ x) :
    |riemannPrimeCounting x - IEANTN.li x - (Chebyshev.psi x - x) / log x| ≤
      evolvedBound x := by
  have hold := RHLimit.Spectral.actual_J_refined_GM hRH hGM hP hJ hx
  unfold evolvedBound
  split_ifs with h15
  · exact le_min hold (actual_J_b5 hRH hGM hP hJ h15)
  · exact hold

lemma preserves_old (x : ℝ) : evolvedBound x ≤ RHLimit.Spectral.refinedBound x := by
  unfold evolvedBound
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem evolved_strict {x : ℝ} (hx : exp 24 ≤ x) :
    (1 / 2 : ℝ) < RHLimit.Spectral.refinedBound x - evolvedBound x := by
  have hx0 : 0 < x := (exp_pos 24).trans_le hx
  have hL : 24 ≤ log x := by
    apply exp_le_exp.mp
    simpa only [exp_log hx0] using hx
  have hg := strict_gain_log hL
  rw [exp_log hx0] at hg
  have h15 : exp (15 : ℝ) ≤ x := (exp_le_exp.mpr (by norm_num : (15 : ℝ) ≤ 24)).trans hx
  unfold evolvedBound
  rw [if_pos h15, min_eq_right (by linarith :
    (1551 / 100 : ℝ) + leading 5 x ≤ RHLimit.Spectral.refinedBound x)]
  exact hg

#print axioms actual_J_evolved
#print axioms evolved_strict
#print axioms preserves_old
end RHOcticPush.GM
