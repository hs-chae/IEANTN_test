import OcticMellinNormalize
import OcticZeroDecomposition

/-! Exact trivial-zero Mellin terms. All integer powers and the actual simple
order of vanishing are retained, without a new explicit-formula assumption. -/
namespace RHOcticPush.TrivialNormalize
open Set MeasureTheory
open RHOcticPush.GreenSource RHOcticPush.PhysicalWeight RHOcticPush.MellinNormalize
open RHOcticPush.ZeroDecomposition
set_option maxHeartbeats 0

lemma cpow_trivial (t : ℝ) (n : ℕ) :
    (t : ℂ) ^ (-2 * ((n : ℂ) + 1)) = (((1 / t ^ 2) ^ (n + 1) : ℝ) : ℂ) := by
  have he : -2 * ((n : ℂ) + 1) = -((2 * (n + 1) : ℕ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.cpow_neg, Complex.cpow_natCast, pow_mul]
  push_cast
  simp only [one_div, inv_pow]

theorem trivial_source_packet (j : ℕ) (C L : ℝ) (n : ℕ) :
    sourcePacket (greenWeight j C L) 2 (trivialZero n) =
      (((∫ t in Set.Ioi (0 : ℝ),
        logWeight j C L t / t * (1 / t ^ 2) ^ (n + 1)) : ℝ) : ℂ) := by
  unfold sourcePacket
  rw [trivial_multiplicity]
  simp only [Int.cast_one, one_mul]
  change (2 : ℂ) ^ (-2 * ((n : ℂ) + 1)) *
    RHOcticPush.GreenSource.mellin (greenWeight j C L) (-2 * ((n : ℂ) + 1)) = _
  rw [green_scale]
  change RHOcticPush.GreenSource.mellin (logWeight j C L) (-2 * ((n : ℂ) + 1)) = _
  unfold RHOcticPush.GreenSource.mellin
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [cpow_trivial]
  push_cast
  ring

#print axioms cpow_trivial
#print axioms trivial_source_packet
end RHOcticPush.TrivialNormalize
