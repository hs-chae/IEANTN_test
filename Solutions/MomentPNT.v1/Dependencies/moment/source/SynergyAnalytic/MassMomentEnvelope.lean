/- Symbolic mass/moment refinements of the SAME paired factor.
No new numerical mass or moment is assumed by an existing ANT theorem here.
Numerical/source instantiation remains a separate obligation. -/
import SynergyAnalytic.BackwardHeightContraction
namespace SynergyAnalytic
open Real Finset
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

noncomputable def totalMass (w : Nat → ℝ) (n : Nat) : ℝ := ∑ i ∈ range n, w i
noncomputable def firstMoment (w D : Nat → ℝ) (n : Nat) : ℝ :=
  ∑ i ∈ range n, w i*D i
noncomputable def unpairedCoefficient (w D : Nat → ℝ) (n : Nat) (L : ℝ) : ℝ :=
  ∑ i ∈ range n, w i*(L/(L-D i))

theorem fraction_antitone {D K L : ℝ} (nonnegative : 0 ≤ D)
    (separated : D < K) (future : K ≤ L) : L/(L-D) ≤ K/(K-D) := by
  have hK : 0 < K-D := sub_pos.mpr separated
  have hL : 0 < L-D := by linarith
  apply (div_le_div_iff₀ hL hK).2
  nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr future)]

theorem fraction_mass_forward {D d K L : ℝ} (nonnegative : 0 ≤ D)
    (lower : d ≤ D) (separated : D < K) (future : K ≤ L) :
    (L-d)*(L/(L-D)) ≤ (K-d)*(K/(K-D))+(L-K) := by
  have hL : L-D ≠ 0 := (by linarith : 0 < L-D).ne'
  have hK : K-D ≠ 0 := (sub_pos.mpr separated).ne'
  have left : (L-d)*(L/(L-D))=L+(D-d)*(L/(L-D)) := by
    field_simp
    <;> ring
  have right : (K-d)*(K/(K-D))=K+(D-d)*(K/(K-D)) := by
    field_simp
    <;> ring
  rw [left,right]
  have compare := mul_le_mul_of_nonneg_left
    (fraction_antitone nonnegative separated future) (sub_nonneg.mpr lower)
  linarith

theorem fraction_mass_backward {D b K L : ℝ} (nonnegative : 0 ≤ D)
    (upper : D ≤ b) (separated : b < L) (past : L ≤ K) :
    (L-b)*(L/(L-D)) ≤ (K-b)*(K/(K-D))-(K-L) := by
  have hL : L-D ≠ 0 := (by linarith : 0 < L-D).ne'
  have hK : K-D ≠ 0 := (by linarith : 0 < K-D).ne'
  have left : (L-b)*(L/(L-D))=L-(b-D)*(L/(L-D)) := by
    field_simp
    <;> ring
  have right : (K-b)*(K/(K-D))=K-(b-D)*(K/(K-D)) := by
    field_simp
    <;> ring
  rw [left,right]
  have compare := mul_le_mul_of_nonneg_left
    (fraction_antitone nonnegative (upper.trans_lt separated) past)
    (sub_nonneg.mpr upper)
  linarith

theorem paired_le_unpaired {w D : Nat → ℝ} {n : Nat} {L : ℝ}
    (weights : ∀ i < n, 0 ≤ w i) (slopes : ∀ i < n, 0 ≤ D i ∧ D i < L) :
    finiteCoefficient w D n L ≤ unpairedCoefficient w D n L := by
  apply sum_le_sum
  intro i hi
  have index := mem_range.mp hi
  exact mul_le_mul_of_nonneg_left
    (pairedFactor_upper_fraction (r:=(1/8:ℝ)) (slopes i index).1 (slopes i index).2)
    (weights i index)

theorem unpaired_anchor_bound {w D : Nat → ℝ} {n : Nat} {K epsilon C : ℝ}
    (weights : ∀ i < n, 0 ≤ w i) (slopes : ∀ i < n, 0 ≤ D i ∧ D i < K)
    (eps_nonnegative : 0 ≤ epsilon) (eps_small : epsilon < 1)
    (small : ∀ i < n, Real.exp (-(K-D i)*(1/8)) ≤ epsilon)
    (checked : finiteCoefficient w D n K ≤ C) :
    unpairedCoefficient w D n K ≤ C/(1-epsilon) := by
  have lower : (1-epsilon)*unpairedCoefficient w D n K ≤ finiteCoefficient w D n K := by
    calc
      _ = ∑ i ∈ range n, w i*((1-epsilon)*(K/(K-D i))) := by
        rw [unpairedCoefficient,mul_sum]
        apply sum_congr rfl
        intro i hi
        ring
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        have index := mem_range.mp hi
        exact mul_le_mul_of_nonneg_left
          (pairedFactor_lower_fraction (slopes i index).1 (slopes i index).2
            eps_nonnegative (small i index)) (weights i index)
  apply (le_div_iff₀ (sub_pos.mpr eps_small)).2
  simpa only [mul_comm] using lower.trans checked

theorem unpaired_mass_forward {w D : Nat → ℝ} {n : Nat} {d K L : ℝ}
    (weights : ∀ i < n, 0 ≤ w i)
    (slopes : ∀ i < n, 0 ≤ D i ∧ d ≤ D i ∧ D i < K) (separated : d < L)
    (future : K ≤ L) :
    unpairedCoefficient w D n L ≤
      ((K-d)*unpairedCoefficient w D n K+(L-K)*totalMass w n)/(L-d) := by
  apply (le_div_iff₀ (sub_pos.mpr separated)).2
  calc
    _ = ∑ i ∈ range n, w i*((L-d)*(L/(L-D i))) := by
      rw [unpairedCoefficient,sum_mul]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ range n, w i*((K-d)*(K/(K-D i))+(L-K)) := by
      apply sum_le_sum
      intro i hi
      have index := mem_range.mp hi
      exact mul_le_mul_of_nonneg_left
        (fraction_mass_forward (slopes i index).1 (slopes i index).2.1
          (slopes i index).2.2 future) (weights i index)
    _ = _ := by
      simp only [unpairedCoefficient,totalMass,mul_sum,mul_add,sum_add_distrib]
      congr 1 <;> apply sum_congr rfl <;> intro i hi <;> ring

theorem unpaired_mass_backward {w D : Nat → ℝ} {n : Nat} {b K L : ℝ}
    (weights : ∀ i < n, 0 ≤ w i) (slopes : ∀ i < n, 0 ≤ D i ∧ D i ≤ b)
    (separated : b < L) (past : L ≤ K) :
    unpairedCoefficient w D n L ≤
      ((K-b)*unpairedCoefficient w D n K-(K-L)*totalMass w n)/(L-b) := by
  apply (le_div_iff₀ (sub_pos.mpr separated)).2
  calc
    _ = ∑ i ∈ range n, w i*((L-b)*(L/(L-D i))) := by
      rw [unpairedCoefficient,sum_mul]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ range n, w i*((K-b)*(K/(K-D i))-(K-L)) := by
      apply sum_le_sum
      intro i hi
      have index := mem_range.mp hi
      exact mul_le_mul_of_nonneg_left
        (fraction_mass_backward (slopes i index).1 (slopes i index).2 separated past)
        (weights i index)
    _ = _ := by
      unfold unpairedCoefficient totalMass
      rw [mul_sum,mul_sum,←sum_sub_distrib]
      apply sum_congr rfl
      intro i hi
      ring

theorem fraction_secant {D a b L : ℝ} (positive : 0 < L)
    (lower : a ≤ D) (upper : D ≤ b) (separated : b < L) :
    L/(L-D) ≤ L*((L-a-b)+D)/((L-a)*(L-b)) := by
  have LD : 0 < L-D := by linarith
  have La : 0 < L-a := by linarith
  have Lb : 0 < L-b := sub_pos.mpr separated
  apply (div_le_div_iff₀ LD (mul_pos La Lb)).2
  nlinarith [mul_nonneg positive.le
    (mul_nonneg (sub_nonneg.mpr lower) (sub_nonneg.mpr upper))]

#print axioms fraction_antitone
#print axioms fraction_mass_forward
#print axioms fraction_mass_backward
#print axioms paired_le_unpaired
#print axioms unpaired_anchor_bound
#print axioms unpaired_mass_forward
#print axioms unpaired_mass_backward
#print axioms fraction_secant
end SynergyAnalytic
