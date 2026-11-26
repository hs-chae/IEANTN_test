/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitSignedLogMoment

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit

private theorem hasDerivAt_neg_inv (u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun u : ℝ => -u⁻¹) (1/u^2) u := by
  have h := (hasDerivAt_const u (-1:ℝ)).div (hasDerivAt_id u) hu
  have heq : ((fun x : ℝ => (-1:ℝ))/id) = (fun x : ℝ => -x⁻¹) := by
    funext x
    simp [div_eq_mul_inv]
  rw [heq] at h
  simpa only [id_eq,zero_mul,neg_mul,one_mul,sub_neg_eq_add,zero_add,neg_div,one_div] using h

private theorem inv_sq_tail :
    IntegrableOn (fun u : ℝ => 1/u^2) (Ioi 1) ∧
      (∫ u in Ioi (1:ℝ), 1/u^2) = 1 := by
  have hd (u : ℝ) (hu : 1 ≤ u) := hasDerivAt_neg_inv u (by linarith)
  have hn (u : ℝ) (hu : 1 < u) : 0 ≤ 1/u^2 := by positivity
  have hl : Tendsto (fun u : ℝ => -u⁻¹) atTop (𝓝 0) := by
    simpa only [neg_zero] using (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0)).neg
  exact ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn hl,
    by simpa using integral_Ioi_of_hasDerivAt_of_nonneg' hd hn hl⟩

/-- A uniform central bound and the sharp quadratic tail imply the exact
half-line derivative mass allowance used in the zero-count remainder. -/
theorem derivative_halfline_envelopes (g : ℝ → ℝ) (hcont : Continuous g)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hcentral : ∀ u ∈ Icc (0:ℝ) 1, |g u| ≤ B)
    (htail : ∀ u : ℝ, 1 < u → |g u| ≤ C/u^2) :
    IntegrableOn (fun u : ℝ => |g u|) (Ioi 0) ∧
    (∫ u in Ioi (0:ℝ), |g u|) ≤ B+C ∧
    IntegrableOn (fun u : ℝ => max 0 (log u)*|g u|) (Ioi 0) ∧
    (∫ u in Ioi (0:ℝ), max 0 (log u)*|g u|) ≤ C := by
  have h01 : IntegrableOn (fun u : ℝ => |g u|) (Ioc 0 1) := hcont.abs.integrableOn_Ioc
  have h1 : IntegrableOn (fun u : ℝ => |g u|) (Ioi 1) := by
    apply (inv_sq_tail.1.const_mul C).mono'
    · exact hcont.abs.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      simpa only [Real.norm_eq_abs,abs_abs,mul_one_div] using htail u hu
  have hlog1 : IntegrableOn (fun u : ℝ => max 0 (log u)*|g u|) (Ioi 1) := by
    apply (integrable_log_div_sq_tail.const_mul C).mono'
    · exact ((measurable_const.max Real.measurable_log).mul hcont.abs.measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      change 1 < u at hu
      have hlu := Real.log_nonneg hu.le
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),max_eq_right hlu]
      calc
        log u*|g u| ≤ log u*(C/u^2) := mul_le_mul_of_nonneg_left (htail u hu) hlu
        _ = C*(log u/u^2) := by ring
  have hlog01 : IntegrableOn (fun u : ℝ => max 0 (log u)*|g u|) (Ioc 0 1) := by
    have hz : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Ioc 0 1) volume := integrableOn_zero
    apply hz.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    simp only [max_eq_left (Real.log_nonpos hu.1.le hu.2),zero_mul]
  have hs : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext u
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h|h) <;> linarith
    · intro h
      by_cases hh : u ≤ 1
      · exact Or.inl ⟨h,hh⟩
      · exact Or.inr (lt_of_not_ge hh)
  have hd : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := by
    rw [disjoint_left]
    intro u hu hv
    exact (not_lt_of_ge hu.2) hv
  have hm := setIntegral_mono_on h01 ((continuous_const : Continuous (fun _ : ℝ => B)).integrableOn_Ioc) measurableSet_Ioc
    (fun u hu => hcentral u ⟨hu.1.le,hu.2⟩)
  have ht := setIntegral_mono_on h1 (inv_sq_tail.1.const_mul C) measurableSet_Ioi (fun u hu => by
    simpa only [mul_one_div] using htail u hu)
  have hlt := setIntegral_mono_on hlog1 (integrable_log_div_sq_tail.const_mul C) measurableSet_Ioi (fun u hu => by
    rw [max_eq_right (Real.log_nonneg hu.le)]
    convert mul_le_mul_of_nonneg_left (htail u hu) (Real.log_nonneg hu.le) using 1 <;> ring)
  rw [integral_const_mul,inv_sq_tail.2,mul_one] at ht
  rw [integral_const_mul,integral_log_div_sq_tail,mul_one] at hlt
  have hsplit := setIntegral_union hd measurableSet_Ioi h01 h1
  have hsplitlog := setIntegral_union hd measurableSet_Ioi hlog01 hlog1
  rw [hs] at hsplit hsplitlog
  have hz : (∫ u in Ioc (0:ℝ) 1, max 0 (log u)*|g u|) = 0 := by
    calc
      _ = ∫ _u in Ioc (0:ℝ) 1, (0:ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        simp only [max_eq_left (Real.log_nonpos hu.1.le hu.2),zero_mul]
      _ = 0 := by simp
  rw [hz,zero_add] at hsplitlog
  have hconst : (∫ u in Ioc (0:ℝ) 1, B) = B := by simp
  rw [hconst] at hm
  exact ⟨by simpa only [hs] using h01.union h1,
    by rw [hsplit]; linarith,
    by simpa only [hs] using hlog01.union hlog1,
    by rw [hsplitlog]; exact hlt⟩

#print axioms derivative_halfline_envelopes
end RH080Next.Explicit
