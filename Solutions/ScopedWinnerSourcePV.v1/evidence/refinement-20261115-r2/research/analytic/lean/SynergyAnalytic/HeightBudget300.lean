/- Combine the original330 finite sum with proved backward contraction and tails. -/
import SynergyAnalytic.BackwardHeightContraction
import SynergyAnalytic.SpectralBase300
namespace SynergyAnalytic
open Real Finset
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem height_spectral_budget_300 {a c D : Nat → ℝ} {n : Nat}
    (weights : ∀ i < n, 0 ≤ (1/a i-1/a (i+1))*c i)
    (slopes : ∀ i < n, 0 ≤ D i ∧ D i ≤ 163)
    (checked : 2*(∑ i ∈ Finset.range n,
      ((1/a i-1/a (i+1))*c i)*pairedFactor (D i) (1/8) 330) ≤
        8433850764/1000000000000) :
    spectralBase 300 100+profileCoefficient a c D n 300 ≤ 935466375/100000000000 := by
  have checkedFinite : finiteCoefficient (fun i=>2*((1/a i-1/a (i+1))*c i)) D n 330 ≤
      8433850764/1000000000000 := by
    rw [finiteCoefficient_height_form]
    exact checked
  have finite := finiteCoefficient_backward
    (fun i hi=>mul_nonneg (by norm_num : (0:ℝ)≤2) (weights i hi))
    slopes checkedFinite (by norm_num : (300:ℝ)≤300) (by norm_num : (300:ℝ)≤330)
  rw [finiteCoefficient_height_form] at finite
  have tail := pairedFactor_upper_fraction (D:=160) (r:=(1/8:ℝ))
    (by norm_num) (by norm_num : (160:ℝ)<300)
  have count := pairedFactor_upper_fraction (D:=(880/3:ℝ)) (r:=(1/8:ℝ))
    (by norm_num) (by norm_num : (880/3:ℝ)<300)
  have base := spectralBase_300_tiny
  unfold profileCoefficient
  norm_num [backwardContractionFactor] at finite tail count
  simp only [one_div] at finite ⊢
  nlinarith

#print axioms height_spectral_budget_300
end SynergyAnalytic
