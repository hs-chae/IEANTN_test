import SynergyAnalytic.TangentMoments
import SynergyAnalytic.BasisCertificate
import SynergyAnalytic.UpperRectangles
namespace SynergyAnalytic
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0

noncomputable def tangentSum (left right:ℝ) (n j:ℕ) : ℝ :=
  ∑i∈range n,tangentUpper (uniformEdge left right n i)
    (tangentNewton2 (uniformEdge left right n i)) ((right-left)/n) j

 theorem integral_le_cell_bounds {f:ℝ→ℝ} {a:ℕ→ℝ} {caps:ℕ→ℝ} {n:ℕ}
    (ha:Monotone a) (hf:ContinuousOn f (Icc (a 0) (a n)))
    (hcaps:∀i<n,(∫x in a i..a (i+1),f x) ≤ caps i) :
    (∫x in a 0..a n,f x) ≤ ∑i∈range n,caps i := by
  have hi : ∀i<n,IntervalIntegrable f volume (a i) (a (i+1)) := by
    intro i hin
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (ha (Nat.le_succ i))]
    exact hf.mono (Icc_subset_Icc (ha (Nat.zero_le i)) (ha hin))
  rw [←intervalIntegral.sum_integral_adjacent_intervals hi]
  apply sum_le_sum
  intro i hi
  exact hcaps i (mem_range.mp hi)

 theorem uniformEdge_width (left right:ℝ) (n i:ℕ) :
    uniformEdge left right n (i+1)=uniformEdge left right n i+(right-left)/n := by
  unfold uniformEdge
  push_cast
  ring
 theorem uniformEdge_ge_start {left right:ℝ} (hspan:left ≤ right) (n i:ℕ) :
    left ≤ uniformEdge left right n i := by
  unfold uniformEdge
  have hn : 0 ≤ (right-left)*(i:ℝ)/(n:ℝ) := by positivity
  linarith

 theorem tangent_uniform_integral {left right:ℝ} {n j:ℕ}
    (hl:1 ≤ left) (hspan:left ≤ right) (hn:0 < n) (hj:j ≤ 2) :
    (∫x in left..right,baseWeight x*(Real.log x)^j) ≤ tangentSum left right n j := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h0 : uniformEdge left right n 0=left := by simp [uniformEdge]
  have hlast : uniformEdge left right n n=right := by simp [uniformEdge,hn0]
  have hf : ContinuousOn (fun x:ℝ=>baseWeight x*(Real.log x)^j) (Icc left right) := by
    intro x hx
    have hp : 0 < x := by linarith [hx.1]
    exact baseWeight_continuous.continuousAt.continuousWithinAt.mul
      ((Real.continuousAt_log hp.ne').pow j).continuousWithinAt
  have hh:=integral_le_cell_bounds (n:=n) (a:=uniformEdge left right n)
    (caps:=fun i=>tangentUpper (uniformEdge left right n i)
      (tangentNewton2 (uniformEdge left right n i)) ((right-left)/n) j)
    (uniformEdge_monotone hspan n) (by simpa only [h0,hlast] using hf) (by
      intro i hi
      rw [uniformEdge_width]
      have hp:=uniformEdge_ge_start hspan n i
      exact tangent_basis_cell_upper (hl.trans hp)
        (tangentNewton2_pos (by linarith)) (by positivity) hj)
  simpa only [h0,hlast,tangentSum] using hh

 theorem tangent_prefix_integral {n:ℕ} (hn:0 < n) :
    (∫x in (5/6:ℝ)..1,baseWeight x) ≤ tangentSum (5/6) 1 n 0 := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h0 : uniformEdge (5/6) 1 n 0=(5/6:ℝ) := by simp [uniformEdge]
  have hlast : uniformEdge (5/6) 1 n n=(1:ℝ) := by simp [uniformEdge,hn0]
  have hh:=integral_le_cell_bounds (n:=n) (a:=uniformEdge (5/6:ℝ) 1 n)
    (caps:=fun i=>tangentUpper (uniformEdge (5/6) 1 n i)
      (tangentNewton2 (uniformEdge (5/6) 1 n i)) ((1-5/6)/n) 0)
    (uniformEdge_monotone (by norm_num : (5/6:ℝ) ≤ 1) n)
    (baseWeight_continuous.continuousOn) (by
      intro i hi
      rw [uniformEdge_width]
      have hp : (5/6:ℝ) ≤ uniformEdge (5/6) 1 n i := uniformEdge_ge_start (by norm_num) n i
      exact tangent_prefix_cell_upper (by linarith)
        (tangentNewton2_pos (by linarith)) (by positivity))
  simpa only [h0,hlast,tangentSum] using hh

/-- Exact finite residuals computed by the NEW source program. These three
closed real expressions contain no integrals, density premise or desired PNT
conclusion. Their source-linked numeric proof is still a separate obligation. -/
noncomputable def tangentBasisZero (pre n:ℕ) : ℝ :=
  universalPeak*(5/6)+tangentSum (5/6) 1 pre 0+tangentSum 1 16 n 0+cubicTail 16
noncomputable def tangentBasisOne (n:ℕ) : ℝ := tangentSum 1 16 n 1+cubicTail 16
noncomputable def tangentBasisTwo (n:ℕ) : ℝ := tangentSum 1 16 n 2+cubicTail 16

 theorem basis_caps_from_tangent_sums {pre n:ℕ} (hp:0 < pre) (hn:0 < n)
    {j0 j1 j2:ℝ} (h0:tangentBasisZero pre n ≤ j0)
    (h1:tangentBasisOne n ≤ j1) (h2:tangentBasisTwo n ≤ j2) :
    UniversalBasisCaps j0 j1 j2 := by
  apply basis_caps_of_three_finite
  · have hprefix:=tangent_prefix_integral hp
    have hshared:=tangent_uniform_integral (left:=1) (right:=16) (j:=0)
      (by norm_num) (by norm_num) hn (by norm_num)
    simp only [pow_zero,mul_one] at hshared
    have hsplit:=intervalIntegral.integral_add_adjacent_intervals
      (baseWeight_continuous.intervalIntegrable (μ:=volume) (5/6) 1)
      (baseWeight_continuous.intervalIntegrable 1 16)
    unfold tangentBasisZero at h0
    linarith
  · have hh:=tangent_uniform_integral (left:=1) (right:=16) (j:=1)
      (by norm_num) (by norm_num) hn (by norm_num)
    simp only [pow_one] at hh
    unfold tangentBasisOne at h1
    linarith
  · have hh:=tangent_uniform_integral (left:=1) (right:=16) (j:=2)
      (by norm_num) (by norm_num) hn (by norm_num)
    unfold tangentBasisTwo at h2
    linarith

#print axioms basis_caps_from_tangent_sums
end SynergyAnalytic
