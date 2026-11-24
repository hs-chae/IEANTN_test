import NicolasSpectralMass
import ActualGMClosed

/-! Positive zero weights give a joint arithmetic envelope, rather than three
independent applications of a scalar absolute bound. No new source is assumed. -/
namespace RHOcticPush.Nicolas
open Real Complex Set NicolasContinuation RHLimit.NicolasMass
abbrev Zero := NicolasContinuation.Zero
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def cosineTerm (x : ℝ) (z : Zero) : ℝ :=
  weight z * Real.cos (z.val.im * Real.log x)

lemma phase_real (hRH : RiemannHypothesis) (x : ℝ) (z : Zero) :
    (phaseTerm x z).re = cosineTerm x z := by
  unfold phaseTerm cosineTerm
  rw [coefficient_ofReal hRH z]
  simp [Complex.exp_re]

lemma phase_summable (hRH : RiemannHypothesis)
    (hN : SourceNicolas119) (x : ℝ) : Summable (phaseTerm x) := by
  have hw := weight_summable hRH hN
  have hn : Summable (fun z : Zero => ‖phaseTerm x z‖) :=
    hw.congr (fun z => (phase_norm hRH x z).symm)
  exact hn.of_norm

lemma cosine_summable (hRH : RiemannHypothesis)
    (hN : SourceNicolas119) (x : ℝ) : Summable (cosineTerm x) := by
  have hs := Complex.reCLM.summable (phase_summable hRH hN x)
  exact hs.congr (phase_real hRH x)

lemma W_eq (hRH : RiemannHypothesis) (hN : SourceNicolas119)
    {x : ℝ} (hx : 0 < x) : W x = ∑' z : Zero, cosineTerm x z := by
  have he : (∑' z : Zero, spectralTerm x z) = ∑' z : Zero, phaseTerm x z :=
    tsum_congr (source_term_eq_phase hx)
  unfold W
  rw [he, Complex.re_tsum (phase_summable hRH hN x)]
  exact tsum_congr (phase_real hRH x)

/-- The two harmonics are coupled: their joint minimum is -3/2, not -3. -/
lemma two_harmonics (t : ℝ) : -(3 / 2 : ℝ) ≤ 2 * Real.cos t + Real.cos (2 * t) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (Real.cos t + 1 / 2)]

lemma pointwise (x : ℝ) (z : Zero) :
    -(3 / 2 : ℝ) * weight z ≤ 2 * cosineTerm x z + cosineTerm (x ^ 2) z := by
  have h := mul_le_mul_of_nonneg_left (two_harmonics (z.val.im * Real.log x))
    (weight_nonneg z)
  unfold cosineTerm
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have he : z.val.im * (2 * Real.log x) = 2 * (z.val.im * Real.log x) := by ring
  rw [he]
  nlinarith

/-- Full infinite sums, including actual multiplicities. The same Nicolas
source supplies summability; the gain is a newly proved positive-kernel step. -/
theorem spectral_pair (hRH : RiemannHypothesis) (hN : SourceNicolas119)
    {x : ℝ} (hx : 0 < x) :
    -(3 / 2 : ℝ) * beta ≤ 2 * W x + W (x ^ 2) := by
  have hw := weight_summable hRH hN
  have h1 := cosine_summable hRH hN x
  have h2 := cosine_summable hRH hN (x ^ 2)
  have hp := (hw.mul_left (-(3 / 2 : ℝ))).tsum_le_tsum
    (fun z : Zero => pointwise x z) ((h1.mul_left 2).add h2)
  rw [tsum_mul_left, (h1.mul_left 2).tsum_add h2, tsum_mul_left] at hp
  rw [W_eq hRH hN hx, W_eq hRH hN (sq_pos_of_pos hx)]
  linarith [mass_le_beta hRH hN]

noncomputable def scaledLogProduct (x : ℝ) : ℝ :=
  Real.sqrt x * Real.log x *
    Real.log (product x / (Real.exp Real.eulerMascheroniConstant *
      Real.log (Chebyshev.theta x)))

noncomputable def penalty (x : ℝ) : ℝ :=
  (2 + beta) / Real.log x + 4 * beta / (Real.log x) ^ 2 +
    Real.sqrt x * Real.log x / (2 * (x - 1))

lemma retains_phase (hRH : RiemannHypothesis) (h219 : SourceNicolas219)
    {x : ℝ} (hx : 599 < x) :
    2 + W x - penalty x ≤ scaledLogProduct x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have he : 2 + W x - penalty x =
      (Real.sqrt x * Real.log x) * ((W x + 2) / (Real.sqrt x * Real.log x) -
        (2 + beta) / (Real.sqrt x * (Real.log x) ^ 2) -
        4 * beta / (Real.sqrt x * (Real.log x) ^ 3) - 1 / (2 * (x - 1))) := by
    unfold penalty
    field_simp [hs.ne', hL.ne', show x - 1 ≠ 0 by linarith]
    <;> ring
  rw [he]
  have hh := h219 hRH x hx
  simp only [neg_div] at hh
  have hbound : (W x + 2) / (Real.sqrt x * Real.log x) -
        (2 + beta) / (Real.sqrt x * (Real.log x) ^ 2) -
        4 * beta / (Real.sqrt x * (Real.log x) ^ 3) - 1 / (2 * (x - 1)) ≤
      -Real.log (f x) := by linarith
  calc
    _ ≤ (Real.sqrt x * Real.log x) * (-Real.log (f x)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = scaledLogProduct x := by
      unfold scaledLogProduct
      rw [log_ratio_eq (by linarith : (3 : ℝ) ≤ x)]

noncomputable def pairedEnvelope (x : ℝ) : ℝ :=
  6 - (3 / 2 : ℝ) * beta - 2 * penalty x - penalty (x ^ 2)

/-- Actual prime products at two arguments, on the full real ray. This is a
joint theorem; it does not assert a stronger one-point Nicolas record. -/
theorem actual_product_pair (hRH : RiemannHypothesis) (h119 : SourceNicolas119)
    (h219 : SourceNicolas219) {x : ℝ} (hx : 599 < x) :
    pairedEnvelope x ≤ 2 * scaledLogProduct x + scaledLogProduct (x ^ 2) := by
  have hx2 : 599 < x ^ 2 := by nlinarith
  have h1 := retains_phase hRH h219 hx
  have h2 := retains_phase hRH h219 hx2
  have hp := spectral_pair hRH h119 (by linarith : (0 : ℝ) < x)
  unfold pairedEnvelope
  linarith

/-- Exact same-premise gain over independently applying the old source profile
at x twice and at x² once, with every lower-order term retained. -/
theorem envelope_identity (x : ℝ) :
    pairedEnvelope x = 2 * profile x + profile (x ^ 2) + (3 / 2 : ℝ) * beta := by
  unfold pairedEnvelope profile penalty
  ring

#print axioms spectral_pair
#print axioms actual_product_pair
#print axioms envelope_identity
end RHOcticPush.Nicolas
