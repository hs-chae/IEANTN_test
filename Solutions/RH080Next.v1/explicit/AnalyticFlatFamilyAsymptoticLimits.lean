/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlatFamilyPopulation
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Filter
open scoped Topology
namespace RH080Next.AnalyticFlatFamilyAsymptotic
open RH080Next.AnalyticFlatFamily

/-- Positive integer mesh for every real density. Only eventual positive
 densities enter the analytic asymptotics. -/
def mesh (α : ℝ) : ℕ := ⌊(Real.pi/2)*α⌋₊+1

def radius (α : ℝ) : ℝ := order (mesh α)

def constant : ℝ := (2+Real.log (2*Real.pi))/Real.pi

theorem mesh_positive (α : ℝ) : 0<mesh α := by unfold mesh; omega

theorem radius_positive (α : ℝ) : 0<radius α :=
  lt_of_lt_of_le (by norm_num) (order_ge_one _ (mesh_positive α))

theorem radius_ratio_tendsto :
    Tendsto (fun α : ℝ => radius α/α) atTop (𝓝 Real.pi) := by
  have hf : Tendsto (fun α : ℝ => (⌊(Real.pi/2)*α⌋₊:ℝ)/α) atTop (𝓝 (Real.pi/2)) :=
    tendsto_nat_floor_mul_div_atTop (by positivity)
  have hi : Tendsto (fun α : ℝ => (1:ℝ)/α) atTop (𝓝 0) :=
    by simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x:ℝ => x⁻¹) atTop (𝓝 0))
  convert (hf.const_mul 2).add hi using 1
  · ext α
    simp only [radius,order,mesh,Nat.cast_add,Nat.cast_one]
    ring
  · ring

theorem radius_tendsto_atTop : Tendsto radius atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((b+1)/Real.pi)] with α hα
  have hf:=Nat.lt_floor_add_one ((Real.pi/2)*α)
  have hp : b+1≤α*Real.pi := (div_le_iff₀ Real.pi_pos).mp hα
  unfold radius order mesh
  push_cast
  linarith

theorem alpha_div_radius_tendsto :
    Tendsto (fun α : ℝ => α/radius α) atTop (𝓝 (1/Real.pi)) := by
  simpa only [one_div,inv_div] using radius_ratio_tendsto.inv₀ Real.pi_ne_zero

theorem inv_radius_tendsto :
    Tendsto (fun α : ℝ => 1/radius α) atTop (𝓝 (0:ℝ)) :=
  by simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp radius_tendsto_atTop)

theorem log_radius_div_radius_tendsto :
    Tendsto (fun α : ℝ => Real.log (radius α)/radius α) atTop (𝓝 (0:ℝ)) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp radius_tendsto_atTop

theorem log_ratio_tendsto :
    Tendsto (fun α : ℝ => Real.log (2*(radius α/α))) atTop
      (𝓝 (Real.log (2*Real.pi))) := by
  exact (Real.continuousAt_log (by positivity : (2:ℝ)*Real.pi≠0)).tendsto.comp
    (radius_ratio_tendsto.const_mul 2)

theorem logarithmic_remainder_tendsto :
    Tendsto (fun α : ℝ => (1+Real.log (2*radius α))/(Real.pi*radius α))
      atTop (𝓝 (0:ℝ)) := by
  have h := ((inv_radius_tendsto.const_mul (1+Real.log 2)).add
    log_radius_div_radius_tendsto).div_const Real.pi
  simp only [mul_zero,zero_add,zero_div] at h
  apply h.congr'
  filter_upwards with α
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (radius_positive α).ne']
  ring

/-- Exact decomposition on the positive density domain; the logarithm uses
 the positive ratio, not any totalized out-of-domain convention. -/
theorem width_offset_identity (α : ℝ) (hα : 0<α) :
    width (mesh α) α-α-Real.log α/Real.pi =
      α/radius α+(1+Real.log (2*(radius α/α)))/Real.pi+
        (1+Real.log (2*radius α))/(Real.pi*radius α) := by
  have hr : 0<radius α := radius_positive α
  have hlog : Real.log (2*(radius α/α)) = Real.log (2*radius α)-Real.log α := by
    rw [show 2*(radius α/α)=(2*radius α)/α by ring,
      Real.log_div (by positivity : 2*radius α≠0) hα.ne']
  have hm : 2*(mesh α:ℝ)=radius α+1 := by unfold radius order; ring
  have hm4 : 4*(mesh α:ℝ)-2=2*radius α := by unfold radius order; ring
  unfold width
  rw [hm4,hlog]
  change (2*(mesh α:ℝ)/radius α)*(α+(1+Real.log (2*radius α))/Real.pi)-α-Real.log α/Real.pi=_
  rw [hm]
  field_simp
  <;> ring

theorem width_offset_tendsto :
    Tendsto (fun α : ℝ => width (mesh α) α-α-Real.log α/Real.pi)
      atTop (𝓝 constant) := by
  have h := (alpha_div_radius_tendsto.add
    (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1)).add log_ratio_tendsto).div_const Real.pi)).add
      logarithmic_remainder_tendsto
  have hk : (1/Real.pi+(1+Real.log (2*Real.pi))/Real.pi)+(0:ℝ)=constant := by
    unfold constant
    ring
  rw [hk] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with α hα
  exact (width_offset_identity α hα).symm

#print axioms width_offset_tendsto
end RH080Next.AnalyticFlatFamilyAsymptotic
