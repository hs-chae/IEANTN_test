/- Symbolic refinement cycle only. Concrete source-verified mass/moment providers
are NOT supplied by this module and no new numerical bound is admitted. -/
import SynergyAnalytic.MassMomentEnvelope
namespace SynergyAnalytic
open Real Finset
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

noncomputable def massForwardEnvelope (C M L : ℝ) : ℝ :=
  (253*(C/(1-1/100000000))+(L-330)*M)/(L-77)
noncomputable def massBackwardEnvelope (C m L : ℝ) : ℝ :=
  (167*(C/(1-1/100000000))-(330-L)*m)/(L-163)
noncomputable def momentEnvelope (M0 M1 L : ℝ) : ℝ :=
  L*((L-240)*M0+M1)/((L-77)*(L-163))

theorem unpaired_anchor330_bound {w D : Nat → ℝ} {n : Nat} {C : ℝ}
    (weights : ∀ i < n, 0 ≤ w i) (slopes : ∀ i < n, 77 ≤ D i ∧ D i ≤ 163)
    (checked : finiteCoefficient w D n 330 ≤ C) :
    unpairedCoefficient w D n 330 ≤ C/(1-1/100000000) := by
  apply unpaired_anchor_bound weights
    (fun i hi=>⟨(by norm_num : (0:ℝ) ≤ 77).trans (slopes i hi).1,by
      have := (slopes i hi).2
      linarith⟩) (by norm_num) (by norm_num) _ checked
  intro i hi
  convert slope_exponential_small (slopes i hi).2 using 1 <;> ring

theorem finiteCoefficient_mass_future {w D : Nat → ℝ} {n : Nat} {C M L : ℝ}
    (weights : ∀ i < n, 0 ≤ w i) (slopes : ∀ i < n, 77 ≤ D i ∧ D i ≤ 163)
    (checked : finiteCoefficient w D n 330 ≤ C) (mass : totalMass w n ≤ M)
    (future : 330 ≤ L) : finiteCoefficient w D n L ≤ massForwardEnvelope C M L := by
  have G := unpaired_anchor330_bound weights slopes checked
  have source := unpaired_mass_forward (d:=77) (K:=330) (L:=L) weights
    (fun i hi=>⟨(by norm_num : (0:ℝ) ≤ 77).trans (slopes i hi).1,
      (slopes i hi).1,by have := (slopes i hi).2; linarith⟩) (by linarith) future
  have paired := paired_le_unpaired (L:=L) weights (fun i hi=>
    ⟨(by norm_num : (0:ℝ) ≤ 77).trans (slopes i hi).1,by
      have := (slopes i hi).2
      linarith⟩)
  apply paired.trans (source.trans _)
  unfold massForwardEnvelope
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ L-77)
  have first := mul_le_mul_of_nonneg_left G (by norm_num : (0:ℝ) ≤ 330-77)
  have second := mul_le_mul_of_nonneg_left mass (sub_nonneg.mpr future)
  norm_num only [show (330:ℝ)-77=253 by norm_num] at first ⊢
  exact add_le_add first second

theorem finiteCoefficient_mass_past {w D : Nat → ℝ} {n : Nat} {C m L : ℝ}
    (weights : ∀ i < n, 0 ≤ w i) (slopes : ∀ i < n, 77 ≤ D i ∧ D i ≤ 163)
    (checked : finiteCoefficient w D n 330 ≤ C) (mass : m ≤ totalMass w n)
    (lowerL : 300 ≤ L) (past : L ≤ 330) :
    finiteCoefficient w D n L ≤ massBackwardEnvelope C m L := by
  have G := unpaired_anchor330_bound weights slopes checked
  have source := unpaired_mass_backward (b:=163) (K:=330) (L:=L) weights
    (fun i hi=>⟨(by norm_num : (0:ℝ) ≤ 77).trans (slopes i hi).1,
      (slopes i hi).2⟩) (by linarith) past
  have paired := paired_le_unpaired (L:=L) weights (fun i hi=>
    ⟨(by norm_num : (0:ℝ) ≤ 77).trans (slopes i hi).1,by
      have := (slopes i hi).2
      linarith⟩)
  apply paired.trans (source.trans _)
  unfold massBackwardEnvelope
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ L-163)
  have first := mul_le_mul_of_nonneg_left G (by norm_num : (0:ℝ) ≤ 330-163)
  have second := mul_le_mul_of_nonneg_left mass (sub_nonneg.mpr past)
  norm_num only [show (330:ℝ)-163=167 by norm_num] at first ⊢
  exact sub_le_sub first second

theorem unpaired_first_moment {w D : Nat → ℝ} {n : Nat} {L : ℝ}
    (weights : ∀ i < n, 0 ≤ w i) (slopes : ∀ i < n, 77 ≤ D i ∧ D i ≤ 163)
    (lowerL : 300 ≤ L) : unpairedCoefficient w D n L ≤
      L*((L-240)*totalMass w n+firstMoment w D n)/((L-77)*(L-163)) := by
  calc
    _ ≤ ∑ i ∈ range n, w i*(L*((L-77-163)+D i)/((L-77)*(L-163))) := by
      apply sum_le_sum
      intro i hi
      have index := mem_range.mp hi
      exact mul_le_mul_of_nonneg_left
        (fraction_secant (by linarith : 0 < L) (slopes i index).1
          (slopes i index).2 (by linarith)) (weights i index)
    _ = _ := by
      have row (i : Nat) : w i*(L*((L-77-163)+D i)/((L-77)*(L-163)))=
          (L*(L-240)/((L-77)*(L-163)))*w i+
            (L/((L-77)*(L-163)))*(w i*D i) := by ring
      simp_rw [row]
      rw [sum_add_distrib,←mul_sum,←mul_sum]
      unfold totalMass firstMoment
      ring

theorem finiteCoefficient_moment_bound {w D : Nat → ℝ} {n : Nat} {M0 M1 L : ℝ}
    (weights : ∀ i < n, 0 ≤ w i) (slopes : ∀ i < n, 77 ≤ D i ∧ D i ≤ 163)
    (mass : totalMass w n ≤ M0) (moment : firstMoment w D n ≤ M1)
    (lowerL : 300 ≤ L) : finiteCoefficient w D n L ≤ momentEnvelope M0 M1 L := by
  have paired := paired_le_unpaired (L:=L) weights (fun i hi=>
    ⟨(by norm_num : (0:ℝ) ≤ 77).trans (slopes i hi).1,by
      have := (slopes i hi).2
      linarith⟩)
  apply paired.trans ((unpaired_first_moment weights slopes lowerL).trans _)
  unfold momentEnvelope
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by linarith) (by linarith))
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ L)
  exact add_le_add (mul_le_mul_of_nonneg_left mass (by linarith)) moment

#print axioms unpaired_anchor330_bound
#print axioms finiteCoefficient_mass_future
#print axioms finiteCoefficient_mass_past
#print axioms unpaired_first_moment
#print axioms finiteCoefficient_moment_bound
end SynergyAnalytic
