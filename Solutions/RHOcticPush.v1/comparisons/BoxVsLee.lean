import IEANTN.Vocabulary.RHOcticEvolution
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Pure whole-function comparison against precisely Lee--Nosal v4,
printed p2 Theorems1.1 and1.2(Eq2). These are two displayed functions;
no complete published minimum or independent height family is claimed.
The actual improved Box second-moment cap is70871/100000 throughout. -/
namespace RHOcticPush.BoxLeeComparison
open Real

noncomputable def lee11 (L : ℝ) : ℝ :=
  L * (L / (8 * π) - (1 / (2 * π) + (293/200 : ℝ) / L) * log L + 493/400)
noncomputable def lee12 (L : ℝ) : ℝ := L * (L - log L) / (8 * π)

lemma log_lower {L : ℝ} (hL : 35 ≤ L) : (7 / 2 : ℝ) ≤ log L := by
  have he : exp 1 ≤ (11/4 : ℝ) := le_of_lt (lt_trans exp_one_lt_d9 (by norm_num))
  have hp := pow_le_pow_left₀ (le_of_lt (exp_pos 1)) he 7
  have hsq : exp (7 / 2 : ℝ) ^ 2 = exp 1 ^ 7 := by
    rw [← exp_nat_mul, ← exp_nat_mul]
    norm_num
  have hb : exp (7 / 2 : ℝ) ≤ 35 := by
    nlinarith [exp_pos (7 / 2 : ℝ)]
  exact (le_log_iff_exp_le (by linarith)).mpr (hb.trans hL)

lemma exp_cubic {z : ℝ} (hz : 0 ≤ z) :
    1 + z + z^2/2 + z^3/6 ≤ exp z := by
  simpa [Finset.sum_range_succ, Nat.factorial] using sum_le_exp_of_nonneg hz 4

lemma cubic12_positive {z : ℝ} (hz : (7 / 2 : ℝ) ≤ z) :
    0 < (1 + z + z^2/2 + z^3/6) * (3*z/4 - 17/10) - z^2 - 23/10 := by
  have hy : 0 ≤ z - 7/2 := by linarith
  have hid : (1 + z + z^2/2 + z^3/6) * (3*z/4 - 17/10) - z^2 - 23/10 =
      725/384 + (517/32)*(z-7/2) + (181/20)*(z-7/2)^2 +
        (221/120)*(z-7/2)^3 + (1/8)*(z-7/2)^4 := by ring
  rw [hid]
  positivity

lemma cubic11_positive {z : ℝ} (hz : (7 / 2 : ℝ) ≤ z) :
    0 < 4*(1 + z + z^2/2 + z^3/6) - z^2 - 10*z - 3 := by
  have hy : 0 ≤ z - 7/2 := by linarith
  have hid : 4*(1 + z + z^2/2 + z^3/6) - z^2 - 10*z - 3 =
      125/6 + (51/2)*(z-7/2) + 8*(z-7/2)^2 + (2/3)*(z-7/2)^3 := by ring
  rw [hid]
  positivity

lemma scaled12_positive {L : ℝ} (hL : 35 ≤ L) :
    0 < L*(3*log L/4 - 1 - log 2) - (log L)^2 +
      2*log 2*log L - (2*(70871/100000 : ℝ) + (28/100)*π) := by
  have hz := log_lower hL
  have hz0 : 0 ≤ log L := by linarith
  have hl0 : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  have hl7 : log (2:ℝ) ≤ 7/10 := le_of_lt (lt_trans log_two_lt_d9 (by norm_num))
  have hpi := pi_lt_d2
  have hL0 : 0 < L := by linarith
  have he := exp_cubic hz0
  rw [exp_log hL0] at he
  have hp : 0 ≤ 3*log L/4 - 17/10 := by linarith
  have hm := mul_le_mul_of_nonneg_right he hp
  have hh := cubic12_positive hz
  have hc : 2*(70871/100000 : ℝ) + (28/100)*π < 23/10 := by linarith
  have hpos : 0 ≤ 2*log 2*log L := by positivity
  have hcmp : L*(3*log L/4 - 17/10) ≤ L*(3*log L/4 - 1 - log 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hL0)
  nlinarith only [hm, hh, hc, hpos, hcmp]

lemma scaled11_positive {L : ℝ} (hL : 35 ≤ L) :
    0 < L*(2*π*(493/400 : ℝ) - 1 - log 2) - (log L)^2 +
      (2*log 2 - 2*π*(293/200 : ℝ))*log L -
        (2*(70871/100000 : ℝ) + (28/100)*π) := by
  have hz := log_lower hL
  have hz0 : 0 ≤ log L := by linarith
  have hl0 : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  have hl7 : log (2:ℝ) ≤ 7/10 := le_of_lt (lt_trans log_two_lt_d9 (by norm_num))
  have hpi := pi_lt_d2
  have hpi3 := pi_gt_three
  have hL0 : 0 < L := by linarith
  have he := exp_cubic hz0
  rw [exp_log hL0] at he
  have hh := cubic11_positive hz
  have hc : 2*(70871/100000 : ℝ) + (28/100)*π < 3 := by linarith
  have ha : 4 ≤ 2*π*(493/400 : ℝ) - 1 - log 2 := by linarith
  have hb : -10 ≤ 2*log 2 - 2*π*(293/200 : ℝ) := by linarith
  have hma := mul_le_mul_of_nonneg_left ha (le_of_lt hL0)
  have hmb := mul_le_mul_of_nonneg_right hb hz0
  nlinarith only [he, hh, hc, hma, hmb]

/-- The actual improved Box function is strictly below Lee--Nosal Theorem 1.2
Eq. (2) throughout the full common log-domain. -/
theorem box_lt_lee12 {L : ℝ} (hL : 35 ≤ L) :
    IEANTN.RHOcticEvolution.boxBound L < lee12 L := by
  have hp : (π:ℝ) ≠ 0 := ne_of_gt pi_pos
  have hid : 2*π*(lee12 L - IEANTN.RHOcticEvolution.boxBound L) =
    L*(3*log L/4 - 1 - log 2) - (log L)^2 +
      2*log 2*log L - (2*(70871/100000 : ℝ) + (28/100)*π) := by
    unfold lee12 IEANTN.RHOcticEvolution.boxBound IEANTN.RHSmoothing.envelope
    unfold IEANTN.RHSmoothing.v
    field_simp
    ring
  have h := scaled12_positive hL
  rw [← hid] at h
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (by positivity : 0 < 2*π)).mp h)

/-- The actual improved Box function is strictly below the precisely displayed
Lee--Nosal Theorem 1.1 function throughout the full common log-domain. -/
theorem box_lt_lee11 {L : ℝ} (hL : 35 ≤ L) :
    IEANTN.RHOcticEvolution.boxBound L < lee11 L := by
  have hp : (π:ℝ) ≠ 0 := ne_of_gt pi_pos
  have hL0 : L ≠ 0 := ne_of_gt (by linarith : 0 < L)
  have hid : 2*π*(lee11 L - IEANTN.RHOcticEvolution.boxBound L) =
    L*(2*π*(493/400 : ℝ) - 1 - log 2) - (log L)^2 +
      (2*log 2 - 2*π*(293/200 : ℝ))*log L -
        (2*(70871/100000 : ℝ) + (28/100)*π) := by
    unfold lee11 IEANTN.RHOcticEvolution.boxBound IEANTN.RHSmoothing.envelope
    unfold IEANTN.RHSmoothing.v
    field_simp
    ring
  have h := scaled11_positive hL
  rw [← hid] at h
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (by positivity : 0 < 2*π)).mp h)

theorem box_lt_both {L : ℝ} (hL : 35 ≤ L) :
    IEANTN.RHOcticEvolution.boxBound L < min (lee11 L) (lee12 L) :=
  lt_min (box_lt_lee11 hL) (box_lt_lee12 hL)

end RHOcticPush.BoxLeeComparison

#print axioms RHOcticPush.BoxLeeComparison.box_lt_lee11
#print axioms RHOcticPush.BoxLeeComparison.box_lt_lee12
#print axioms RHOcticPush.BoxLeeComparison.box_lt_both
