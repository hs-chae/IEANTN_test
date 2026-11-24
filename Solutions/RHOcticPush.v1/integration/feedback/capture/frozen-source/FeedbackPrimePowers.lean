import FeedbackPiUpper

/-! One-pass feedback into the actual prime-power correction. The isolated
square term is bounded using the previously proved ordinary-prime upper bound;
the original finite floor-height and k>=3 tail are preserved exactly. -/
namespace RHOcticPush.PrimeSquareFeedback
open Real IEANTN RHLimit.PrimePower RHContinuation.Ramanujan RHOcticPush.BoxPerron
set_option maxHeartbeats 0

/-- Conservative feedback retains the old positive exp(L/4)/2 allowance too.
Only the leading square-root coefficient changes from2log4 to11/10. -/
noncomputable def remainder (L : ℝ) : ℝ :=
  (11/10 : ℝ)*Real.exp (L/2)/L+Real.exp (L/4)/2+
    Real.exp (L/3)*Real.log (L/Real.log 2)

lemma actual_square_term (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {L : ℝ} (hL : 100 ≤ L) :
    primeCounting (Real.sqrt (Real.exp L))/2 ≤ (11/10 : ℝ)*Real.exp (L/2)/L := by
  have h0 : L ≠ 0 := by linarith
  have h := prime_counting_upper_log rh hN hI hB (by linarith : (50:ℝ)≤L/2)
  have hh := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤2)
  rw [sqrt_exp_eq]
  convert! hh using 1 <;> field_simp [h0] <;> ring

/-- The real observable J−pi is bounded; no assumed Q-improvement is a premise. -/
theorem actual_remainder_feedback (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {L : ℝ} (hL : 100 ≤ L) :
    riemannPrimeCounting (Real.exp L)-primeCounting (Real.exp L) ≤ remainder L := by
  have hx : (4:ℝ) ≤ Real.exp L :=
    exp_two_ge_four.trans (Real.exp_le_exp.mpr (by linarith : (2:ℝ)≤L))
  have hQ := remainder_upper_with_square hx
  have hs := actual_square_term rh hN hI hB hL
  have he : (Real.exp L)^(1/(3:ℝ)) = Real.exp (L/3) := by
    rw [←Real.exp_mul]
    congr 1
    ring
  rw [he] at hQ
  have ht := mul_le_mul_of_nonneg_left (height_log_bound (by linarith : (2:ℝ)≤L))
    (Real.exp_pos (L/3)).le
  unfold remainder
  linarith [Real.exp_pos (L/4)]

/-- Exact difference of the complete old/new correction functions, including
all unchanged height/floor/prime-power-tail terms. -/
theorem remainder_gain (L : ℝ) :
    elementaryRemainder L-remainder L =
      (2*Real.log 4-(11/10 : ℝ))*Real.exp (L/2)/L := by
  unfold elementaryRemainder remainder
  ring

lemma coefficient_lower : (167/100 : ℝ) < 2*Real.log 4-(11/10) := by
  have he : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_gt_d9]

theorem remainder_strict_gain {L : ℝ} (hL : 100 ≤ L) :
    (167/100 : ℝ)*Real.exp (L/2)/L < elementaryRemainder L-remainder L := by
  rw [remainder_gain]
  have h := mul_lt_mul_of_pos_right coefficient_lower
    (div_pos (Real.exp_pos (L/2)) (by linarith : (0:ℝ)<L))
  convert! h using 1 <;> ring

/-- Complete lower-scale J bound, not its rounded1.1 consequence. -/
noncomputable def rawRemainder (L : ℝ) : ℝ :=
  Jupper (L/2)/2+Real.exp (L/4)/2+Real.exp (L/3)*Real.log (L/Real.log 2)

/-- Preserve the whole original35-ray; actual lower-scale feedback is used only
where its35-onset applies, and a minimum prevents any loss. -/
noncomputable def effectiveRemainder (L : ℝ) : ℝ :=
  if 70 ≤ L then min (elementaryRemainder L) (rawRemainder L)
  else elementaryRemainder L

theorem actual_remainder_raw (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {L : ℝ} (hL : 70 ≤ L) :
    riemannPrimeCounting (Real.exp L)-primeCounting (Real.exp L) ≤ rawRemainder L := by
  have hx : (4:ℝ) ≤ Real.exp L :=
    exp_two_ge_four.trans (Real.exp_le_exp.mpr (by linarith : (2:ℝ)≤L))
  have hQ := remainder_upper_with_square hx
  have hp := prime_counting_upper_full_log rh hN hI hB (by linarith : (35:ℝ)≤L/2)
  have hs := div_le_div_of_nonneg_right hp (by norm_num : (0:ℝ)≤2)
  rw [←sqrt_exp_eq] at hs
  have he : (Real.exp L)^(1/(3:ℝ)) = Real.exp (L/3) := by
    rw [←Real.exp_mul]
    congr 1
    ring
  rw [he] at hQ
  have ht := mul_le_mul_of_nonneg_left (height_log_bound (by linarith : (2:ℝ)≤L))
    (Real.exp_pos (L/3)).le
  unfold rawRemainder
  linarith [Real.exp_pos (L/4)]

theorem actual_remainder_effective (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {L : ℝ} (hL : 35 ≤ L) :
    riemannPrimeCounting (Real.exp L)-primeCounting (Real.exp L) ≤ effectiveRemainder L := by
  unfold effectiveRemainder
  split_ifs with h70
  · exact le_min (actual_remainder_elementary (by linarith : (2:ℝ)≤L))
      (actual_remainder_raw rh hN hI hB h70)
  · exact actual_remainder_elementary (by linarith : (2:ℝ)≤L)

lemma effective_le_old (L : ℝ) : effectiveRemainder L ≤ elementaryRemainder L := by
  unfold effectiveRemainder
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

lemma effective_le_raw {L : ℝ} (hL : 70 ≤ L) :
    effectiveRemainder L ≤ rawRemainder L := by
  rw [effectiveRemainder,if_pos hL]
  exact min_le_right _ _

lemma raw_lt_simplified {L : ℝ} (hL : 100 ≤ L) : rawRemainder L < remainder L := by
  have h0 : L ≠ 0 := by linarith
  have h := Jupper_simplified (by linarith : (50:ℝ)≤L/2)
  have hh := div_lt_div_of_pos_right h (by norm_num : (0:ℝ)<2)
  have he : ((11/10 : ℝ)*(Real.exp (L/2)/(L/2)))/2 =
      (11/10 : ℝ)*Real.exp (L/2)/L := by field_simp [h0] <;> ring
  rw [he] at hh
  unfold rawRemainder remainder
  linarith

lemma effective_lt_simplified {L : ℝ} (hL : 100 ≤ L) :
    effectiveRemainder L < remainder L :=
  (effective_le_raw (by linarith : (70:ℝ)≤L)).trans_lt (raw_lt_simplified hL)

theorem effective_strict_gain {L : ℝ} (hL : 100 ≤ L) :
    (167/100 : ℝ)*Real.exp (L/2)/L <
      elementaryRemainder L-effectiveRemainder L := by
  have h := remainder_strict_gain hL
  have hr := effective_lt_simplified hL
  linarith

#print axioms actual_square_term
#print axioms actual_remainder_feedback
#print axioms remainder_gain
#print axioms coefficient_lower
#print axioms remainder_strict_gain
#print axioms actual_remainder_raw
#print axioms actual_remainder_effective
#print axioms effective_le_old
#print axioms effective_le_raw
#print axioms raw_lt_simplified
#print axioms effective_lt_simplified
#print axioms effective_strict_gain
end RHOcticPush.PrimeSquareFeedback
