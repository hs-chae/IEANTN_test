/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineSignedMoment
import ExplicitFourierPair

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private theorem split_positive (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0:ℝ)))
    (r : ℝ) (hr : 0 < r) :
    (∫ u in Ioi (0:ℝ), f u) = (∫ u in Ioc (0:ℝ) r, f u)+(∫ u in Ioi r, f u) := by
  have hs : Ioc (0:ℝ) r ∪ Ioi r = Ioi 0 := by
    ext u
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h|h) <;> linarith
    · intro h
      by_cases hh : u ≤ r
      · exact Or.inl ⟨h,hh⟩
      · exact Or.inr (lt_of_not_ge hh)
  have hd : Disjoint (Ioc (0:ℝ) r) (Ioi r) := by
    rw [disjoint_left]
    intro u hu hv
    exact (not_lt_of_ge hu.2) hv
  have h1 := hf.mono_set (show Ioc (0:ℝ) r ⊆ Ioi 0 from fun u hu => hu.1)
  have h2 := hf.mono_set (show Ioi r ⊆ Ioi (0:ℝ) from fun u hu => hr.trans hu)
  simpa only [hs] using setIntegral_union hd measurableSet_Ioi h1 h2

/-- Extending the zero-density main term to the origin keeps the negative
signed logarithmic moment. Only the omitted negative central integral is
charged to the explicit cutoff allowance. -/
theorem truncated_log_density_le (F : ℝ → ℝ) (heven : Function.Even F)
    (hF : Integrable F)
    (hlog : Integrable (fun u : ℝ => |F u| *log |u|))
    (U A d r : ℝ) (hU : (∫ u : ℝ, |F u|) ≤ U)
    (hd : 0 < d) (hd1 : d ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hcap : ∀ u ∈ Icc (0:ℝ) r, |F u| ≤ A) :
    IntegrableOn (fun u : ℝ => log (u/d)*|F u|) (Ioi r) ∧
    2*(∫ u in Ioi r, log (u/d)*|F u|) ≤
      U*log (1/d)+(∫ u : ℝ, |F u| *log |u|)+2*A*r*(1-log r) := by
  let g : ℝ → ℝ := fun u => |F u| *log u
  have hg : IntegrableOn g (Ioi (0:ℝ)) := by
    apply hlog.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [show |u| = u from abs_of_pos hu]
  have hgi := hg.mono_set (show Ioi r ⊆ Ioi (0:ℝ) from fun u hu => hr.trans hu)
  have hfi : IntegrableOn (fun u : ℝ => |F u|) (Ioi r) := hF.abs.integrableOn
  have hdens : IntegrableOn (fun u : ℝ => log (u/d)*|F u|) (Ioi r) := by
    apply (hgi.add (hfi.const_mul (log (1/d)))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 := hr.trans hu
    rw [log_div hu0.ne' hd.ne',log_div one_ne_zero hd.ne',log_one]
    dsimp [g]
    ring
  have heq : (∫ u in Ioi r, log (u/d)*|F u|) =
      (∫ u in Ioi r, g u)+log (1/d)*(∫ u in Ioi r, |F u|) := by
    rw [←integral_const_mul,←integral_add hgi (hfi.const_mul (log (1/d)))]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 := hr.trans hu
    rw [log_div hu0.ne' hd.ne',log_div one_ne_zero hd.ne',log_one]
    dsimp [g]
    ring
  have hnorm : (∫ u : ℝ, |F u|) = 2*(∫ u in Ioi (0:ℝ), |F u|) := by
    have he : (fun u : ℝ => |F u|) = (fun u : ℝ => |F (|u|)|) := by
      funext u
      rcases le_or_gt 0 u with h|h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h,heven u]
    conv_lhs => rw [he]
    exact integral_comp_abs (f := fun u : ℝ => |F u|)
  have hlogeq : (∫ u : ℝ, |F u| *log |u|) = 2*(∫ u in Ioi (0:ℝ), g u) := by
    have he : (fun u : ℝ => |F u| *log |u|) =
        (fun u : ℝ => g |u|) := by
      funext u
      dsimp [g]
      rcases le_or_gt 0 u with h|h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h,heven u]
    rw [he]
    exact integral_comp_abs (f := g)
  have hcuti : IntervalIntegrable g volume 0 r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mpr
      (hg.mono_set (show Ioc (0:ℝ) r ⊆ Ioi 0 from fun u hu => hu.1))
  have hlow : A*(r*log r-r) ≤ ∫ u in Ioc (0:ℝ) r, g u := by
    have hi := intervalIntegral.intervalIntegrable_log' (a := (0:ℝ)) (b := r)
    have hb := intervalIntegral.integral_mono_on hr.le (hi.const_mul A) hcuti (fun u hu => by
      dsimp [g]
      have hl : log u ≤ 0 := log_nonpos hu.1 (hu.2.trans hr1)
      exact mul_le_mul_of_nonpos_right (hcap u hu) hl)
    rw [intervalIntegral.integral_const_mul,integral_log] at hb
    simpa only [zero_mul,sub_zero,add_zero,intervalIntegral.integral_of_le hr.le] using hb
  have hsplit := split_positive g hg r hr
  have hmass : (∫ u in Ioi r, |F u|) ≤ ∫ u in Ioi (0:ℝ), |F u| := by
    apply setIntegral_mono_set hF.abs.integrableOn
    · filter_upwards with u
      exact abs_nonneg _
    · exact ae_of_all _ (fun u hu => hr.trans hu)
  have hld : 0 ≤ log (1/d) := log_nonneg ((one_le_div hd).mpr hd1)
  have hm := mul_le_mul_of_nonneg_left hmass hld
  have hu := mul_le_mul_of_nonneg_right hU hld
  refine ⟨hdens,?_⟩
  rw [heq]
  rw [hnorm] at hu
  rw [hlogeq]
  nlinarith

#print axioms truncated_log_density_le
end RH080Next.Explicit
