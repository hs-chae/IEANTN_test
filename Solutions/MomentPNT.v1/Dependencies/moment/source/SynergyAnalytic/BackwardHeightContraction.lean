/- Valid backward transfer of the same330 computation to300..330.
No new height calculation, Gaussian, density or zero-free premise is introduced. -/
import SynergyAnalytic.RationalHeightEnvelope
namespace SynergyAnalytic
open Real Finset
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem fraction_ratio_backward {D d K L : ℝ}
    (nonnegative : 0 ≤ D) (upper : D ≤ d) (separated : d < L) (past : L ≤ K) :
    L/(L-D) ≤ (L*(K-d)/(K*(L-d)))*(K/(K-D)) := by
  have Lpos : 0 < L := lt_of_le_of_lt (nonnegative.trans upper) separated
  have Kpos : 0 < K := Lpos.trans_le past
  have KD : 0 < K-D := by linarith
  have LD : 0 < L-D := by linarith
  have Ld : 0 < L-d := sub_pos.mpr separated
  have algebra : (L*(K-d)/(K*(L-d)))*(K/(K-D))=
      (L*(K-d))/((L-d)*(K-D)) := by
    field_simp
  rw [algebra]
  apply (div_le_div_iff₀ LD (mul_pos Ld KD)).2
  have positive := mul_nonneg Lpos.le
    (mul_nonneg (sub_nonneg.mpr past) (sub_nonneg.mpr upper))
  nlinarith

theorem pairedFactor_relative_backward {D d r K L epsilon : ℝ}
    (nonnegative : 0 ≤ D) (upper : D ≤ d) (separated : d < L) (past : L ≤ K)
    (eps_nonnegative : 0 ≤ epsilon) (eps_small : epsilon < 1)
    (small : Real.exp (-(K-D)*r) ≤ epsilon) :
    pairedFactor D r L ≤
      (L*(K-d)/(K*(L-d))/(1-epsilon))*pairedFactor D r K := by
  have Lpos : 0 < L := lt_of_le_of_lt (nonnegative.trans upper) separated
  have Kpos : 0 < K := Lpos.trans_le past
  have dK : d < K := separated.trans_le past
  have DK : D < K := upper.trans_lt dK
  have Ld : 0 < L-d := sub_pos.mpr separated
  have eps : 0 < 1-epsilon := sub_pos.mpr eps_small
  let q := L*(K-d)/(K*(L-d))
  have q_nonnegative : 0 ≤ q := div_nonneg
    (mul_nonneg Lpos.le (sub_nonneg.mpr dK.le)) (mul_nonneg Kpos.le Ld.le)
  have amplified := mul_le_mul_of_nonneg_left
    (pairedFactor_lower_fraction nonnegative DK eps_nonnegative small)
    (div_nonneg q_nonnegative eps.le)
  have cancellation : (q/(1-epsilon))*((1-epsilon)*(K/(K-D)))=q*(K/(K-D)) := by
    field_simp
  rw [cancellation] at amplified
  exact (pairedFactor_upper_fraction (r:=r) nonnegative (upper.trans_lt separated)).trans
    ((fraction_ratio_backward nonnegative upper separated past).trans amplified)

noncomputable def backwardContractionFactor (L : ℝ) : ℝ :=
  L*167/(330*(L-163))/(1-1/100000000)

theorem pairedFactor_backward_300_330 {D L : ℝ} (nonnegative : 0 ≤ D)
    (upper : D ≤ 163) (lowerL : 300 ≤ L) (upperL : L ≤ 330) :
    pairedFactor D (1/8) L ≤ backwardContractionFactor L*pairedFactor D (1/8) 330 := by
  have small : Real.exp (-((330:ℝ)-D)*(1/8)) ≤ 1/100000000 := by
    convert slope_exponential_small upper using 1 <;> ring
  simpa only [backwardContractionFactor,show (330:ℝ)-163=167 by norm_num] using
    (pairedFactor_relative_backward (d:=163) (K:=330)
      nonnegative upper (by linarith) upperL (by norm_num) (by norm_num) small)

theorem finiteCoefficient_backward {w D : Nat → ℝ} {n : Nat} {C L : ℝ}
    (weights : ∀ i < n, 0 ≤ w i) (slopes : ∀ i < n, 0 ≤ D i ∧ D i ≤ 163)
    (checked : finiteCoefficient w D n 330 ≤ C) (lowerL : 300 ≤ L) (upperL : L ≤ 330) :
    finiteCoefficient w D n L ≤ backwardContractionFactor L*C := by
  have factor : 0 ≤ backwardContractionFactor L := by
    unfold backwardContractionFactor
    have positiveL : 0 < L := by linarith
    have separated : 0 < L-163 := by linarith
    positivity
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        w i*(backwardContractionFactor L*pairedFactor (D i) (1/8) 330) := by
      apply Finset.sum_le_sum
      intro i member
      have hi := Finset.mem_range.mp member
      exact mul_le_mul_of_nonneg_left
        (pairedFactor_backward_300_330 (slopes i hi).1 (slopes i hi).2 lowerL upperL)
        (weights i hi)
    _ = backwardContractionFactor L*finiteCoefficient w D n 330 := by
      unfold finiteCoefficient
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i member
      ring
    _ ≤ backwardContractionFactor L*C := mul_le_mul_of_nonneg_left checked factor

#print axioms fraction_ratio_backward
#print axioms pairedFactor_relative_backward
#print axioms pairedFactor_backward_300_330
#print axioms finiteCoefficient_backward
end SynergyAnalytic
