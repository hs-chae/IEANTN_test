import Scaled40Physical
set_option autoImplicit false
noncomputable section
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
namespace RH080Next.Scaled40
open RH080.Gaussian40

theorem physicalG_even (x : ℝ) : physicalG (-x)=physicalG x := by
  simp only [physicalG, mul_neg]
  exact congrArg (fun y : ℝ => (4/5)*y)
    (RH080Next.Scaled40Fourier.physicalG_even ((4/5)*x))

theorem physicalG_abs (x : ℝ) : physicalG |x|=physicalG x := by
  by_cases hx : 0≤x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), physicalG_even]

theorem physical_wings_identity :
    (∫ x in {x : ℝ | 1< |x| }, max 0 (physicalG x)) =
      2*(∫ x in Ioi (1 : ℝ), max 0 (physicalG x)) := by
  have hs : MeasurableSet {x : ℝ | 1< |x| } :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [← integral_indicator hs]
  have hpoint (x : ℝ) :
      ({x : ℝ | 1< |x| }).indicator (fun x => max 0 (physicalG x)) x =
      (Ioi (1 : ℝ)).indicator (fun x => max 0 (physicalG x)) |x| := by
    simp only [Set.indicator_apply, mem_ofPred_eq, mem_Ioi, physicalG_abs]
  simp_rw [hpoint]
  rw [integral_comp_abs, setIntegral_indicator measurableSet_Ioi]
  have heq : Ioi (0 : ℝ)∩Ioi 1=Ioi 1 := by
    apply inter_eq_right.mpr
    intro x hx
    change (1 : ℝ)<x at hx
    change (0 : ℝ)<x
    linarith
  rw [heq]

theorem physical_full_wings_upper :
    (∫ x in {x : ℝ | 1< |x| }, max 0 (physicalG x)) ≤ (313227945/10000000000 : ℝ) := by
  rw [physical_wings_identity]
  exact physical_positive_wing_upper

noncomputable def physicalFullInverseObjective : ℝ :=
  (∫ x : ℝ, |physicalF x|)/
    (physicalF 0-(36/11 : ℝ)*(∫ x in {x : ℝ | 1< |x| }, max 0 (physicalG x)))

theorem physical_denominator_pos :
    0<physicalF 0-(36/11 : ℝ)*(∫ x in {x : ℝ | 1< |x| }, max 0 (physicalG x)) := by
  nlinarith [physicalF_zero_exact, physical_full_wings_upper]

theorem physical_full_objective_upper :
    physicalFullInverseObjective ≤ (20582561296/24680948495 : ℝ) := by
  unfold physicalFullInverseObjective
  apply (div_le_iff₀ physical_denominator_pos).mpr
  nlinarith [physical_norm_upper, physicalF_zero_exact, physical_full_wings_upper]

theorem physical_full_objective_lt_readable :
    physicalFullInverseObjective < (833945313/1000000000 : ℝ) :=
  physical_full_objective_upper.trans_lt (by norm_num)

theorem strict_improvement_over_previous :
    (20582561296/24680948495 : ℝ)<82325773717/98718416336 := by norm_num

#print axioms physical_full_wings_upper
#print axioms physical_denominator_pos
#print axioms physical_full_objective_upper
#print axioms strict_improvement_over_previous
end RH080Next.Scaled40
