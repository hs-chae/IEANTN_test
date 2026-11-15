import SynergyAnalytic.Basis
namespace SynergyAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

/-- Reuses the exact algebraic sixth-power tangent already proved in the
historical density_nplus/AnalyticMajorants.lean; no numerical premise. -/
theorem cube_root_quadratic_tangent (x a:ℝ) (hx:0 ≤ x) (ha:0 < a) :
    x^((1:ℝ)/3) ≤ 5*a/6+x^2/(6*a^5) := by
  let z:=x^((1:ℝ)/3)
  have hz : 0 ≤ z := Real.rpow_nonneg hx _
  have hf : 0 ≤ (z-a)^2*(z^4+2*a*z^3+3*a^2*z^2+4*a^3*z+5*a^4) := by positivity
  have he : z^6=x^2 := by
    dsimp [z]
    rw [←Real.rpow_natCast,←Real.rpow_mul hx]
    norm_num
  have hh : 6*a^5*z ≤ x^2+5*a^6 := by nlinarith only [hf,he]
  have hrep : 5*a/6+x^2/(6*a^5)=(5*a^6+x^2)/(6*a^5) := by field_simp <;> ring
  rw [hrep]
  apply (le_div_iff₀ (show 0 < 6*a^5 by positivity)).mpr
  dsimp [z] at hh
  nlinarith only [hh]

noncomputable def rootTangent (left a v:ℝ) : ℝ :=
  5*a/6+(left+v)^2/(6*a^5)
noncomputable def logTangent (left v:ℝ) : ℝ := Real.log left+v/left
noncomputable def tangentKernel (left a:ℝ) (j:ℕ) (v:ℝ) : ℝ :=
  Real.exp (-(601/2500:ℝ)*left^2)*Real.exp (-(2*(601/2500:ℝ)*left)*v)*
    rootTangent left a v*(logTangent left v)^j

theorem log_tangent_bound {left v:ℝ} (hl:0 < left) (hv:0 ≤ v) :
    Real.log (left+v) ≤ logTangent left v := by
  have hx : 0 < left+v := by linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos hx hl)
  rw [Real.log_div hx.ne' hl.ne'] at hh
  have he : (left+v)/left-1=v/left := by field_simp <;> ring
  rw [he] at hh
  unfold logTangent
  linarith

theorem gaussian_left_tangent {left v q:ℝ} (hq:0 ≤ q) :
    Real.exp (-q*(left+v)^2) ≤ Real.exp (-q*left^2)*Real.exp (-(2*q*left)*v) := by
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hq (sq_nonneg v)]

theorem base_left_tangent {left a v:ℝ} (hl:0 ≤ left) (ha:0 < a) (hv:0 ≤ v) :
    baseWeight (left+v) ≤
      Real.exp (-(601/2500:ℝ)*left^2)*Real.exp (-(2*(601/2500:ℝ)*left)*v)*rootTangent left a v := by
  have hroot := cube_root_quadratic_tangent (left+v) a (by linarith) ha
  have hg := gaussian_left_tangent (left:=left) (v:=v) (q:=601/2500) (by norm_num)
  exact mul_le_mul hg hroot (Real.rpow_nonneg (by linarith) _) (by positivity)

theorem log_basis_left_tangent {left a v:ℝ} (hl:1 ≤ left) (ha:0 < a) (hv:0 ≤ v) (j:ℕ) :
    baseWeight (left+v)*(Real.log (left+v))^j ≤ tangentKernel left a j v := by
  have hb:=base_left_tangent (by linarith : 0 ≤ left) ha hv
  have hp:=pow_le_pow_left₀ (Real.log_nonneg (by linarith : 1 ≤ left+v))
    (log_tangent_bound (by linarith) hv) j
  have hh:=mul_le_mul hb hp (pow_nonneg (Real.log_nonneg (by linarith : 1 ≤ left+v)) j)
    (by unfold rootTangent;positivity)
  exact hh

theorem tangentKernel_continuous {left a:ℝ} (j:ℕ) : Continuous (tangentKernel left a j) := by
  unfold tangentKernel rootTangent logTangent
  fun_prop

/-- A whole-interval upper bound. It is second-order in cell width, and its
positive polynomial/exponential integral has a finite exact moment formula. -/
theorem tangent_basis_cell_integral {left a width:ℝ}
    (hl:1 ≤ left) (ha:0 < a) (hw:0 ≤ width) (j:ℕ) :
    (∫x in left..left+width,baseWeight x*(Real.log x)^j) ≤
      ∫v in (0:ℝ)..width,tangentKernel left a j v := by
  have hfun : ContinuousOn (fun v:ℝ=>baseWeight (left+v)*(Real.log (left+v))^j) (Icc 0 width) := by
    intro v hv
    have hp : 0 < left+v := by linarith [hv.1]
    exact (baseWeight_continuous.continuousAt.comp (continuousAt_const.add continuousAt_id)).continuousWithinAt.mul
      (((Real.continuousAt_log hp.ne').comp (continuousAt_const.add continuousAt_id)).pow j).continuousWithinAt
  have hi : IntervalIntegrable (fun v:ℝ=>baseWeight (left+v)*(Real.log (left+v))^j) volume 0 width := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hw] using hfun
  have hm:=intervalIntegral.integral_mono_on hw hi
    ((tangentKernel_continuous j).intervalIntegrable 0 width)
    (by intro v hv;exact log_basis_left_tangent hl ha hv.1 j)
  have he:=intervalIntegral.integral_comp_add_right
    (fun x:ℝ=>baseWeight x*(Real.log x)^j) (a:=0) (b:=width) left
  rw [zero_add] at he
  rw [add_comm width left] at he
  rw [←he]
  simpa only [add_comm left,add_comm width] using hm

#print axioms log_basis_left_tangent
#print axioms tangent_basis_cell_integral
end SynergyAnalytic
