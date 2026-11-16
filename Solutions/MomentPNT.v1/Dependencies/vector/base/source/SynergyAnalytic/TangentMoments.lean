import SynergyAnalytic.TangentCells
import SynergyAnalytic.ExponentialMoments
namespace SynergyAnalytic
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0
set_option maxRecDepth 20000

noncomputable def rootCoefficient (left a:ℝ) (k:ℕ) : ℝ :=
  if k=0 then 5*a/6+left^2/(6*a^5)
  else if k=1 then 2*left/(6*a^5)
  else if k=2 then 1/(6*a^5) else 0
noncomputable def tangentCoefficient (left a:ℝ) : ℕ→ℕ→ℝ
  | 0,k=>rootCoefficient left a k
  | j+1,k=>tangentCoefficient left a j k*Real.log left+
      if k=0 then 0 else tangentCoefficient left a j (k-1)/left

/-- Exactly the source's positive coefficient convolution, with no dropped
nonzero coefficient at the only three requested powers0,1,2. -/
theorem tangentCoefficient_polynomial (left a v:ℝ) {j:ℕ} (hj:j ≤ 2) :
    (∑k∈range 5,tangentCoefficient left a j k*v^k)=
      rootTangent left a v*(logTangent left v)^j := by
  interval_cases j <;>
    norm_num [tangentCoefficient,rootCoefficient,sum_range_succ,rootTangent,logTangent] <;> ring

noncomputable def tangentUpper (left a width:ℝ) (j:ℕ) : ℝ :=
  Real.exp (-(601/2500:ℝ)*left^2)*
    ∑k∈range 5,tangentCoefficient left a j k*
      exponentialMoment k (2*(601/2500:ℝ)*left) width

theorem tangentKernel_integral {left a width:ℝ} (hl:0 < left) {j:ℕ} (hj:j ≤ 2) :
    (∫v in (0:ℝ)..width,tangentKernel left a j v)=tangentUpper left a width j := by
  have hrate : 2*(601/2500:ℝ)*left ≠ 0 := by positivity
  have he : ∀v:ℝ,tangentKernel left a j v=
      Real.exp (-(601/2500:ℝ)*left^2)*
        ∑k∈range 5,tangentCoefficient left a j k*
          (v^k*Real.exp (-(2*(601/2500:ℝ)*left)*v)) := by
    intro v
    have hp:=tangentCoefficient_polynomial left a v hj
    unfold tangentKernel
    simp_rw [←mul_assoc]
    rw [←sum_mul,hp]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum (by
    intro k hk
    exact ((by fun_prop : Continuous (fun v:ℝ=>tangentCoefficient left a j k*
      (v^k*Real.exp (-(2*(601/2500:ℝ)*left)*v))))).intervalIntegrable 0 width)]
  unfold tangentUpper
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_const_mul,exponentialMoment_integral hrate]

theorem tangent_basis_cell_upper {left a width:ℝ}
    (hl:1 ≤ left) (ha:0 < a) (hw:0 ≤ width) {j:ℕ} (hj:j ≤ 2) :
    (∫x in left..left+width,baseWeight x*(Real.log x)^j) ≤ tangentUpper left a width j := by
  exact (tangent_basis_cell_integral hl ha hw j).trans_eq
    (tangentKernel_integral (by linarith) hj)

/-- The prefix5/6..1 uses no logarithm and needs only a positive left endpoint. -/
theorem tangent_prefix_cell_upper {left a width:ℝ}
    (hl:0 < left) (ha:0 < a) (hw:0 ≤ width) :
    (∫x in left..left+width,baseWeight x) ≤ tangentUpper left a width 0 := by
  have hc : Continuous (fun v:ℝ=>baseWeight (left+v)) :=
    baseWeight_continuous.comp (continuous_const.add continuous_id)
  have hm : (∫v in (0:ℝ)..width,baseWeight (left+v)) ≤
      ∫v in (0:ℝ)..width,tangentKernel left a 0 v :=
    intervalIntegral.integral_mono_on hw (hc.intervalIntegrable 0 width)
    ((tangentKernel_continuous 0).intervalIntegrable 0 width)
    (by intro v hv;simpa only [tangentKernel,pow_zero,mul_one] using base_left_tangent hl.le ha hv.1)
  have he:=intervalIntegral.integral_comp_add_right baseWeight (a:=0) (b:=width) left
  rw [zero_add,add_comm width left] at he
  rw [←he]
  have hh : (∫v in (0:ℝ)..width,baseWeight (v+left)) ≤
      ∫v in (0:ℝ)..width,tangentKernel left a 0 v := by simpa only [add_comm left] using hm
  exact hh.trans_eq (tangentKernel_integral hl (by norm_num))

/-- Two positive rational updates are sufficient as a source parameter
construction. No root-approximation or convergence theorem is required. -/
noncomputable def tangentSeed (left:ℝ) : ℝ := (left+2)/3
noncomputable def tangentUpdate (left a:ℝ) : ℝ := (2*a+left/a^2)/3
noncomputable def tangentNewton2 (left:ℝ) : ℝ :=
  tangentUpdate left (tangentUpdate left (tangentSeed left))
theorem tangentNewton2_pos {left:ℝ} (hl:0 < left) : 0 < tangentNewton2 left := by
  have hs : 0 < tangentSeed left := by unfold tangentSeed;positivity
  have hu : 0 < tangentUpdate left (tangentSeed left) := by unfold tangentUpdate;positivity
  unfold tangentNewton2 tangentUpdate
  positivity

#print axioms tangent_basis_cell_upper
#print axioms tangent_prefix_cell_upper
#print axioms tangentNewton2_pos
end SynergyAnalytic
