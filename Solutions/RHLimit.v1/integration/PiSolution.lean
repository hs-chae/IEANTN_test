import SourceBoxPi
import IEANTN.Nodes.RHPrimeCounting.v2.Conclusions
namespace RHPrimeCounting.v2
open Real IEANTN RHLimit.PurePi RHLimit.PrimePower RHLimit.Spectral
set_option maxHeartbeats 0

theorem challenge_elementary_prime_powers : elementary_prime_powers :=
  fun _ hL => actual_remainder_elementary hL

theorem challenge_refined_transfer (rh : RH.v1.hypothesis) (hg : RHPrimeCounting.v1.gm_source)
    (hp : Buthe.v1.theorem_2_psi) (hj : Buthe.v1.theorem_2_li_minus_riemann_pi) :
    refined_transfer := fun _ hx => actual_J_refined_GM rh hg hp hj hx

theorem challenge_transfer_gain : transfer_gain :=
  fun _ hx => by
    simpa [v1.transferCorrection, refinedCorrection,
      RHContinuation.Ramanujan.gmSqrtLog, refinedBound, refinedLeading,
      div_eq_mul_inv, mul_assoc] using refined_strictly_improves_old hx

theorem challenge_ch_Epi (rh : RH.v1.hypothesis) (hg : RHPrimeCounting.v1.gm_source)
    (hp : Buthe.v1.theorem_2_psi) (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hch : RHSmoothing.v1.recovered_ch_psi) : ch_Epi := by
  intro L hL
  have hpsi := hch (exp L) (exp_le_exp.mpr hL)
  rw [log_exp, mul_comm] at hpsi
  have h := actual_Epi_elementary rh hg hp hj RHSmoothing.chBound (by linarith) hpsi
  rw [normalized_formula _ (by linarith)] at h
  exact h

theorem challenge_box_Epi (rh : RH.v1.hypothesis) (hg : RHPrimeCounting.v1.gm_source)
    (hp : Buthe.v1.theorem_2_psi) (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hbox : RHSmoothing.v1.box_psi) : box_Epi := by
  intro L hL
  have hpsi := hbox (exp L) (exp_le_exp.mpr hL)
  rw [log_exp] at hpsi
  have h := actual_Epi_elementary rh hg hp hj RHSmoothing.fastBound (by linarith) hpsi
  rw [normalized_formula _ (by linarith)] at h
  exact h

theorem challenge_ch_classical_gain (rh : RH.v1.hypothesis)
    (hg : RHPrimeCounting.v1.gm_source) (hp : Buthe.v1.theorem_2_psi)
    (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hch : RHSmoothing.v1.recovered_ch_psi) : ch_classical_gain := by
  intro L hL
  have hpsi := hch (exp L) (exp_le_exp.mpr (by linarith : 34 ≤ L))
  rw [log_exp, mul_comm] at hpsi
  have hb := actual_pi_Li_elementary rh hg hp hj RHSmoothing.chBound (by linarith) hpsi
  have hco := ch_normalized_improves_classical hL
  have hL0 : 0 < L := by linarith
  have he : RHLimit.PurePi.envelope RHSmoothing.chBound L+2 =
      normalized RHSmoothing.chBound L*(exp (L/2)/L) := by
    unfold normalized
    field_simp [hL0.ne',exp_ne_zero]
  calc
    _ ≤ RHLimit.PurePi.envelope RHSmoothing.chBound L+2 := hb
    _ = normalized RHSmoothing.chBound L*(exp (L/2)/L) := he
    _ < (L^2/(8*π)-L/3)*(exp (L/2)/L) :=
      mul_lt_mul_of_pos_right hco (div_pos (exp_pos _) hL0)
    _ = exp (L/2)*(L/(8*π)-1/3) := by field_simp [hL0.ne']

theorem challenge_box_point_100 (rh : RH.v1.hypothesis)
    (hg : RHPrimeCounting.v1.gm_source) (hp : Buthe.v1.theorem_2_psi)
    (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hbox : RHSmoothing.v1.box_psi) : box_point_100 := by
  have hpsi := hbox (exp 100) (exp_le_exp.mpr (by norm_num : (35:ℝ)≤100))
  rw [log_exp] at hpsi
  have h := actual_Epi_elementary rh hg hp hj RHSmoothing.fastBound
    (by norm_num : (12:ℝ)≤100) hpsi
  norm_num at h
  exact h.trans_lt (mul_lt_mul_of_pos_right box_at_100 (exp_pos (-50:ℝ)))

#print axioms challenge_elementary_prime_powers
#print axioms challenge_refined_transfer
#print axioms challenge_transfer_gain
#print axioms challenge_ch_Epi
#print axioms challenge_box_Epi
#print axioms challenge_ch_classical_gain
#print axioms challenge_box_point_100
end RHPrimeCounting.v2
