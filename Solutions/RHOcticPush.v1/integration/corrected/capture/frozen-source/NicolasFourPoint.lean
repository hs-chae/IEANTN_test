import NicolasMultipoint

/-! A four-height Fejer polynomial retains more spectral information than the
scalar published bound. The resulting conclusion concerns actual prime products. -/
namespace RHOcticPush.Nicolas
open Real Complex NicolasContinuation RHLimit.NicolasMass
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma gamma_gt_54 : (54 / 100 : ℝ) < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 16
  have hb : (54 / 100 : ℝ) < Real.eulerMascheroniSeq 16 := by
    norm_num [Real.eulerMascheroniSeq, harmonic, Finset.sum_range_succ]
    interval_decide 80 (trust := kernel) <;> ring
  exact hb.trans h

lemma beta_pos : 0 < beta := by
  have hp : Real.log Real.pi < (1145 / 1000 : ℝ) := by
    interval_decide 80 (trust := kernel)
  unfold beta
  linarith [gamma_gt_54, Real.log_two_lt_d9]

theorem pair_strictly_improves (x : ℝ) :
    2 * profile x + profile (x ^ 2) < pairedEnvelope x := by
  rw [envelope_identity]
  linarith [beta_pos]

lemma four_harmonics (t : ℝ) :
    -(5 / 2 : ℝ) ≤ 4 * Real.cos t + 3 * Real.cos (2 * t) +
      2 * Real.cos (3 * t) + Real.cos (4 * t) := by
  rw [show (4 : ℝ) * t = 2 * (2 * t) by ring]
  simp only [Real.cos_two_mul, Real.cos_three_mul]
  nlinarith [sq_nonneg (4 * Real.cos t ^ 2 + 2 * Real.cos t - 1)]

lemma cosine_power (x : ℝ) (k : ℕ) (z : NicolasContinuation.Zero) :
    cosineTerm (x ^ k) z = weight z * Real.cos ((k : ℝ) * (z.val.im * Real.log x)) := by
  unfold cosineTerm
  rw [Real.log_pow]
  congr 2
  ring

lemma pointwise_four (x : ℝ) (z : NicolasContinuation.Zero) :
    -(5 / 2 : ℝ) * weight z ≤ 4 * cosineTerm x z + 3 * cosineTerm (x ^ 2) z +
      2 * cosineTerm (x ^ 3) z + cosineTerm (x ^ 4) z := by
  have h := mul_le_mul_of_nonneg_left (four_harmonics (z.val.im * Real.log x))
    (weight_nonneg z)
  rw [cosine_power, cosine_power, cosine_power]
  norm_num only [Nat.cast_ofNat]
  unfold cosineTerm
  nlinarith

/-- Full four-height spectral inequality with actual multiplicities and full
infinite-series convergence. The independent scalar cost would be10beta. -/
theorem spectral_four (hRH : RiemannHypothesis) (hN : SourceNicolas119)
    {x : ℝ} (hx : 0 < x) :
    -(5 / 2 : ℝ) * beta ≤ 4 * W x + 3 * W (x ^ 2) + 2 * W (x ^ 3) + W (x ^ 4) := by
  have hw := weight_summable hRH hN
  have h1 := cosine_summable hRH hN x
  have h2 := cosine_summable hRH hN (x ^ 2)
  have h3 := cosine_summable hRH hN (x ^ 3)
  have h4 := cosine_summable hRH hN (x ^ 4)
  have hp := (hw.mul_left (-(5 / 2 : ℝ))).tsum_le_tsum
    (fun z : NicolasContinuation.Zero => pointwise_four x z)
    ((((h1.mul_left 4).add (h2.mul_left 3)).add (h3.mul_left 2)).add h4)
  rw [tsum_mul_left,
    (((h1.mul_left 4).add (h2.mul_left 3)).add (h3.mul_left 2)).tsum_add h4,
    ((h1.mul_left 4).add (h2.mul_left 3)).tsum_add (h3.mul_left 2),
    (h1.mul_left 4).tsum_add (h2.mul_left 3), tsum_mul_left, tsum_mul_left,
    tsum_mul_left] at hp
  rw [W_eq hRH hN hx, W_eq hRH hN (pow_pos hx 2), W_eq hRH hN (pow_pos hx 3),
    W_eq hRH hN (pow_pos hx 4)]
  linarith [mass_le_beta hRH hN]

noncomputable def fourEnvelope (x : ℝ) : ℝ :=
  20 - (5 / 2 : ℝ) * beta - 4 * penalty x - 3 * penalty (x ^ 2) -
    2 * penalty (x ^ 3) - penalty (x ^ 4)

theorem actual_product_four (hRH : RiemannHypothesis) (h119 : SourceNicolas119)
    (h219 : SourceNicolas219) {x : ℝ} (hx : 599 < x) :
    fourEnvelope x ≤ 4 * scaledLogProduct x + 3 * scaledLogProduct (x ^ 2) +
      2 * scaledLogProduct (x ^ 3) + scaledLogProduct (x ^ 4) := by
  have hx2 : 599 < x ^ 2 := by nlinarith
  have hx3 : 599 < x ^ 3 := by nlinarith [sq_nonneg x]
  have hx4 : 599 < x ^ 4 := by nlinarith [sq_nonneg (x ^ 2)]
  have h1 := retains_phase hRH h219 hx
  have h2 := retains_phase hRH h219 hx2
  have h3 := retains_phase hRH h219 hx3
  have h4 := retains_phase hRH h219 hx4
  have hp := spectral_four hRH h119 (by linarith : (0 : ℝ) < x)
  unfold fourEnvelope
  linarith

theorem four_envelope_identity (x : ℝ) :
    fourEnvelope x = 4 * profile x + 3 * profile (x ^ 2) + 2 * profile (x ^ 3) +
      profile (x ^ 4) + (15 / 2 : ℝ) * beta := by
  unfold fourEnvelope profile penalty
  ring

theorem four_strictly_improves (x : ℝ) :
    4 * profile x + 3 * profile (x ^ 2) + 2 * profile (x ^ 3) + profile (x ^ 4) <
      fourEnvelope x := by
  rw [four_envelope_identity]
  linarith [beta_pos]

#print axioms beta_pos
#print axioms spectral_four
#print axioms actual_product_four
#print axioms four_strictly_improves
end RHOcticPush.Nicolas
