/- Domain, monotonicity and exact rational checkpoints for the new envelope. -/
import SynergyAnalytic.RationalHeightEnvelope
namespace SynergyAnalytic
open Real Set
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem fraction_antitone {d K L : ℝ}
    (nonnegative : 0 ≤ d) (domain : d < K) (future : K ≤ L) :
    L/(L-d) ≤ K/(K-d) := by
  have KD : 0 < K-d := sub_pos.mpr domain
  have LD : 0 < L-d := by linarith
  have first : L/(L-d)=1+d/(L-d) := by field_simp [LD.ne']; ring
  have second : K/(K-d)=1+d/(K-d) := by field_simp [KD.ne']; ring
  rw [first,second]
  exact add_le_add (le_refl (1:ℝ))
    (div_le_div_of_nonneg_left nonnegative KD (sub_le_sub_right future d))

theorem contractionFactor_fraction {L : ℝ} (future : 330 ≤ L) :
    contractionFactor L=(253/330/(1-1/100000000))*(L/(L-77)) := by
  have denominator : L-77 ≠ 0 := by linarith
  unfold contractionFactor
  field_simp [denominator]

theorem contractionFactor_antitone {K L : ℝ} (domain : 330 ≤ K) (future : K ≤ L) :
    contractionFactor L ≤ contractionFactor K := by
  rw [contractionFactor_fraction (domain.trans future),contractionFactor_fraction domain]
  exact mul_le_mul_of_nonneg_left
    (fraction_antitone (by norm_num : (0:ℝ) ≤ 77) (by linarith : (77:ℝ) < K) future)
    (by norm_num)

theorem rationalHeightCoefficient_antitone {C K L : ℝ} (nonnegative : 0 ≤ C)
    (domain : 330 ≤ K) (future : K ≤ L) :
    rationalHeightCoefficient C L ≤ rationalHeightCoefficient C K := by
  have finite := mul_le_mul_of_nonneg_right (contractionFactor_antitone domain future) nonnegative
  have tail := fraction_antitone (d:=160) (by norm_num) (by linarith : (160:ℝ) < K) future
  have count := fraction_antitone (d:=(880/3:ℝ)) (by norm_num)
    (by linarith : (880/3:ℝ) < K) future
  unfold rationalHeightCoefficient
  simp only [mul_div_assoc]
  nlinarith

theorem rationalHeightCoefficient_nonnegative {C L : ℝ}
    (nonnegative : 0 ≤ C) (future : 330 ≤ L) : 0 ≤ rationalHeightCoefficient C L := by
  have factor := contractionFactor_nonnegative future
  have hL : 0 < L := by linarith
  have tail : 0 < L-160 := by linarith
  have count : 0 < L-880/3 := by linarith
  unfold rationalHeightCoefficient
  positivity

theorem rational_checkpoint_330 :
    rationalHeightCoefficient (8433850764/1000000000000) 330 < 8441646/1000000000 := by
  norm_num [rationalHeightCoefficient,contractionFactor]

theorem rational_checkpoint_500 :
    rationalHeightCoefficient (8433850764/1000000000000) 500 < 7648883/1000000000 := by
  norm_num [rationalHeightCoefficient,contractionFactor]

theorem rational_checkpoint_1000 :
    rationalHeightCoefficient (8433850764/1000000000000) 1000 < 7010158/1000000000 := by
  norm_num [rationalHeightCoefficient,contractionFactor]

theorem rational_checkpoint_1000000 :
    rationalHeightCoefficient (8433850764/1000000000000) 1000000 < 6470481/1000000000 := by
  norm_num [rationalHeightCoefficient,contractionFactor]

#print axioms fraction_antitone
#print axioms contractionFactor_fraction
#print axioms contractionFactor_antitone
#print axioms rationalHeightCoefficient_antitone
#print axioms rationalHeightCoefficient_nonnegative
#print axioms rational_checkpoint_330
#print axioms rational_checkpoint_500
#print axioms rational_checkpoint_1000
#print axioms rational_checkpoint_1000000
end SynergyAnalytic
