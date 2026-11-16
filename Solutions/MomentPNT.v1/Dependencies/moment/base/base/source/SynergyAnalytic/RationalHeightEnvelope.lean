/- Reuse one source-verified330 sum as a rational whole-function envelope.
The quantitative Laplace contraction retains the unchanged source data and premises. -/
import SynergyAnalytic.PairedContraction
import SynergyAnalytic.HeightProfile
namespace SynergyAnalytic
open Real Finset
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

noncomputable def contractionFactor (L : ℝ) : ℝ :=
  L*253/(330*(L-77))/(1-1/100000000)

noncomputable def finiteCoefficient (w D : Nat → ℝ) (n : Nat) (L : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, w i*pairedFactor (D i) (1/8) L

noncomputable def rationalHeightCoefficient (C L : ℝ) : ℝ :=
  (1+1/1000000000)*(1/1000000000000+contractionFactor L*C+
    (1/250000)*L/(L-160)+1/50000000+
    (1/1000000000000)*L/(L-880/3)+1/1000000000000)+
      1/1000000000000+1/100000000

theorem contractionFactor_nonnegative {L : ℝ} (future : 330 ≤ L) :
    0 ≤ contractionFactor L := by
  unfold contractionFactor
  have hL : 0 < L := by linarith
  have hden : 0 < L-77 := by linarith
  positivity

theorem finiteCoefficient_contraction {w D : Nat → ℝ} {n : Nat} {C L : ℝ}
    (weights : ∀ i < n, 0 ≤ w i) (slopes : ∀ i < n, 77 ≤ D i ∧ D i ≤ 163)
    (checked : finiteCoefficient w D n 330 ≤ C) (future : 330 ≤ L) :
    finiteCoefficient w D n L ≤ contractionFactor L*C := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, w i*(contractionFactor L*pairedFactor (D i) (1/8) 330) := by
      apply Finset.sum_le_sum
      intro i member
      have hi := Finset.mem_range.mp member
      exact mul_le_mul_of_nonneg_left
        (pairedFactor_77_163_contraction (slopes i hi).1 (slopes i hi).2 future) (weights i hi)
    _ = contractionFactor L*finiteCoefficient w D n 330 := by
      unfold finiteCoefficient
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i member
      ring
    _ ≤ contractionFactor L*C := mul_le_mul_of_nonneg_left checked
      (contractionFactor_nonnegative future)

theorem finiteCoefficient_height_form (a c D : Nat → ℝ) (n : Nat) (L : ℝ) :
    finiteCoefficient (fun i=>2*((1/a i-1/a (i+1))*c i)) D n L=
      2*(∑ i ∈ Finset.range n, ((1/a i-1/a (i+1))*c i)*pairedFactor (D i) (1/8) L) := by
  unfold finiteCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i member
  ring

theorem profile_rational_bound {a c D : Nat → ℝ} {n : Nat} {C L : ℝ}
    (weights : ∀ i < n, 0 ≤ (1/a i-1/a (i+1))*c i)
    (slopes : ∀ i < n, 77 ≤ D i ∧ D i ≤ 163)
    (checked : 2*(∑ i ∈ Finset.range n,
      ((1/a i-1/a (i+1))*c i)*pairedFactor (D i) (1/8) 330) ≤ C)
    (future : 330 ≤ L) :
    profileCoefficient a c D n L ≤ contractionFactor L*C+
      (1/250000)*L/(L-160)+1/50000000+
      (1/1000000000000)*L/(L-880/3)+1/1000000000000 := by
  have finiteChecked : finiteCoefficient (fun i=>2*((1/a i-1/a (i+1))*c i)) D n 330 ≤ C := by
    rw [finiteCoefficient_height_form]
    exact checked
  have finite := finiteCoefficient_contraction
    (fun i hi=>mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (weights i hi)) slopes finiteChecked future
  rw [finiteCoefficient_height_form] at finite
  have tail := pairedFactor_upper_fraction (D:=160) (r:=(1/8:ℝ))
    (by norm_num) (by linarith : (160:ℝ) < L)
  have count := pairedFactor_upper_fraction (D:=(880/3:ℝ)) (r:=(1/8:ℝ))
    (by norm_num) (by linarith : (880/3:ℝ) < L)
  unfold profileCoefficient
  simp only [mul_div_assoc]
  nlinarith

theorem ray_rational_bound {a c D : Nat → ℝ} {n : Nat} {C L : ℝ}
    (weights : ∀ i < n, 0 ≤ (1/a i-1/a (i+1))*c i)
    (slopes : ∀ i < n, 77 ≤ D i ∧ D i ≤ 163)
    (checked : 2*(∑ i ∈ Finset.range n,
      ((1/a i-1/a (i+1))*c i)*pairedFactor (D i) (1/8) 330) ≤ C)
    (future : 330 ≤ L) :
    rayCoefficient a c D n L ≤ rationalHeightCoefficient C L := by
  have profile := profile_rational_bound weights slopes checked future
  have base := spectralBase_330_tiny
  unfold rayCoefficient rationalHeightCoefficient
  nlinarith

#print axioms contractionFactor_nonnegative
#print axioms finiteCoefficient_contraction
#print axioms finiteCoefficient_height_form
#print axioms profile_rational_bound
#print axioms ray_rational_bound
end SynergyAnalytic
