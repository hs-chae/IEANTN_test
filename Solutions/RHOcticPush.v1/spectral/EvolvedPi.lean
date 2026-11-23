import GMComparison
import PurePiBounds

/-! The proved GM minimum is consumed by ordinary prime counting, including
prime-power and offset-Li corrections. All original source assumptions remain. -/
namespace RHOcticPush.Pi
open Real IEANTN RHContinuation.Ramanujan RHLimit.PrimePower
set_option maxHeartbeats 0

noncomputable def envelope (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  exp (L / 2) / L * f L + RHOcticPush.GM.evolvedBound (exp L) +
    elementaryRemainder L + 2

lemma actual_J (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (f : ℝ → ℝ) {L : ℝ} (hL : 12 ≤ L)
    (hpsi : |Chebyshev.psi (exp L) - exp L| ≤ sqrt (exp L) * f L) :
    |riemannPrimeCounting (exp L) - IEANTN.li (exp L)| ≤
      RHOcticPush.GM.evolvedBound (exp L) + exp (L / 2) / L * f L := by
  have h0 : 0 < L := by linarith
  have hg := RHOcticPush.GM.actual_J_evolved hRH hGM hP hJ (exp_le_exp.mpr hL)
  rw [Real.log_exp] at hg
  have hp : |(Chebyshev.psi (exp L) - exp L) / L| ≤ exp (L / 2) / L * f L := by
    rw [abs_div, abs_of_pos h0]
    have h := div_le_div_of_nonneg_right hpsi h0.le
    rw [← Real.exp_half] at h
    convert! h using 1 <;> ring
  have he : riemannPrimeCounting (exp L) - IEANTN.li (exp L) =
      (riemannPrimeCounting (exp L) - IEANTN.li (exp L) -
        (Chebyshev.psi (exp L) - exp L) / L) +
      (Chebyshev.psi (exp L) - exp L) / L := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hg hp)

theorem actual_Li (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (f : ℝ → ℝ) {L : ℝ} (hL : 12 ≤ L)
    (hpsi : |Chebyshev.psi (exp L) - exp L| ≤ sqrt (exp L) * f L) :
    |primeCounting (exp L) - IEANTN.Li (exp L)| ≤ envelope f L := by
  have hj := actual_J hRH hGM hP hJ f hL hpsi
  have hq := actual_remainder_elementary (by linarith : (2 : ℝ) ≤ L)
  have hq0 := actual_prime_power_nonnegative (exp_pos L)
  have he : primeCounting (exp L) - IEANTN.li (exp L) =
      (riemannPrimeCounting (exp L) - IEANTN.li (exp L)) -
      (riemannPrimeCounting (exp L) - primeCounting (exp L)) := by ring
  have htri := abs_sub_le (riemannPrimeCounting (exp L) - IEANTN.li (exp L)) (0 : ℝ)
    (riemannPrimeCounting (exp L) - primeCounting (exp L))
  simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hq0] at htri
  have hpi : |primeCounting (exp L) - IEANTN.li (exp L)| ≤
      RHOcticPush.GM.evolvedBound (exp L) + exp (L / 2) / L * f L +
        elementaryRemainder L := by
    rw [he]
    linarith
  have hoff := actual_li_Li_offset (one_lt_exp_iff.mpr (by linarith : (0 : ℝ) < L))
  have h2 := RHLimit.PurePi.li_two_bounds
  have he2 : primeCounting (exp L) - IEANTN.Li (exp L) =
      (primeCounting (exp L) - IEANTN.li (exp L)) + IEANTN.li 2 := by linarith
  rw [he2]
  have ht := abs_add_le (primeCounting (exp L) - IEANTN.li (exp L)) (IEANTN.li 2)
  rw [abs_of_nonneg h2.1] at ht
  unfold envelope
  linarith

lemma envelope_gain (f : ℝ → ℝ) (L : ℝ) :
    RHLimit.PurePi.envelope f L + 2 - envelope f L =
      RHLimit.Spectral.refinedBound (exp L) - RHOcticPush.GM.evolvedBound (exp L) := by
  unfold RHLimit.PurePi.envelope envelope RHLimit.Spectral.refinedBound
    RHLimit.Spectral.refinedLeading
  rw [Real.log_exp, ← Real.exp_half]
  ring

theorem strict_gain (f : ℝ → ℝ) {L : ℝ} (hL : 24 ≤ L) :
    (1 / 2 : ℝ) < RHLimit.PurePi.envelope f L + 2 - envelope f L := by
  rw [envelope_gain]
  exact RHOcticPush.GM.evolved_strict (exp_le_exp.mpr hL)

lemma interval_lower {E : ℝ → ℝ} {a b : ℝ}
    (ha : |primeCounting a - IEANTN.Li a| ≤ E a)
    (hb : |primeCounting b - IEANTN.Li b| ≤ E b) :
    IEANTN.Li b - IEANTN.Li a - E a - E b ≤ primeCounting b - primeCounting a := by
  have ha' := (abs_le.mp ha).2
  have hb' := (abs_le.mp hb).1
  linarith

#print axioms actual_Li
#print axioms strict_gain
#print axioms interval_lower
end RHOcticPush.Pi
