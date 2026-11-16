/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityTail
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- The finite density majorant is integrable in the real-part parameter.
Clipping the auxiliary height below H gives a globally continuous extension. -/
theorem finiteDensityWeight_continuous {t : ℝ}
    (ht : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ t) : Continuous (fun σ ↦ finiteDensityWeight σ t) := by
  set H : ℝ := 3 * (10 : ℝ) ^ (12 : ℕ) with hH
  have hH1 : 1 < H := by dsimp [H]; norm_num
  have hbase : Continuous (fun p : ℝ × ℝ ↦ max H p.2) := continuous_const.max continuous_snd
  have hbase1 : ∀ p : ℝ × ℝ, 1 < max H p.2 := fun p ↦ hH1.trans_le (le_max_left _ _)
  have hbase0 : ∀ p : ℝ × ℝ, max H p.2 ≠ 0 := fun p ↦ by have := hbase1 p; linarith
  have hp := hbase.rpow (show Continuous (fun p : ℝ × ℝ ↦ 8 * (1 - p.1) / 3) by fun_prop)
    (fun p ↦ Or.inl (hbase0 p))
  have hl := hbase.log hbase0
  have hq := hl.rpow (show Continuous (fun p : ℝ × ℝ ↦ 5 - 2 * p.1) by fun_prop)
    (fun p ↦ Or.inl (Real.log_pos (hbase1 p)).ne')
  have hnum : Continuous (fun p : ℝ × ℝ ↦ fksDensityMajorant p.1 (max H p.2)) :=
    ((continuous_const.mul hp).mul hq).add (continuous_const.mul (hl.pow 2))
  have hfun : Continuous (fun p : ℝ × ℝ ↦ fksDensityMajorant p.1 (max H p.2) / (max H p.2) ^ 2) :=
    hnum.div (hbase.pow 2) (fun p ↦ pow_ne_zero 2 (hbase0 p))
  have hi : Continuous (fun σ : ℝ ↦ ∫ u in H..t,
      fksDensityMajorant σ (max H u) / (max H u) ^ 2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hfun H t
  have hInt : Continuous (fun σ : ℝ ↦ ∫ u in H..t, fksDensityMajorant σ u / u ^ 2) := by
    convert hi using 1
    funext σ
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    dsimp only
    rw [max_eq_right hu.1]
  have hF : Continuous (fun σ : ℝ ↦ fksDensityMajorant σ t) := by
    have hc := hnum.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ ↦ t)))
    change Continuous (fun σ : ℝ ↦ fksDensityMajorant σ (max H t)) at hc
    simpa only [max_eq_right ht] using hc
  unfold finiteDensityWeight
  exact (continuous_const.mul ((hF.div_const t).add hInt)).add
    ((continuous_const.div_const t).mul hF)

/-- The density-restricted ordinate sum inside the full positive-ordinate rectangle. -/
theorem density_majorant_filter_eq {σ t : ℝ} :
    (∑ ρ ∈ (CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t) le_rfl).toFinset,
      if σ < ρ.re then (t / Real.pi * (1 / ρ.im) + 2) * (IEANTN.zetaOrder ρ : ℝ) else 0) =
    IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t)
      (fun ρ ↦ t / Real.pi * (1 / ρ.im) + 2) := by
  classical
  have hfull := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t) le_rfl
  have hrect := finite_zero_rectangle (Set.Ioo σ 1) (T := t)
  rw [rectangle_sum_eq hrect]
  have he : hrect.toFinset = hfull.toFinset.filter (fun ρ ↦ σ < ρ.re) := by
    ext ρ
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
    constructor
    · intro hρ
      exact ⟨⟨trivial, hρ.2.1, hρ.2.2⟩, hρ.1.1⟩
    · rintro ⟨hρ, hσ⟩
      have hr : ρ.re < 1 := by
        by_contra hh
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hh) hρ.2.2
      exact ⟨⟨hσ, hr⟩, hρ.2.1, hρ.2.2⟩
  rw [he, Finset.sum_filter]

/-- The complete normalized density layer bound for the CH2 spectral majorant. -/
theorem density_spectral_majorant (hFKS : FKS.v3.density_0618)
    (hRH : IEANTN.RiemannHypothesisUpTo (3 * (10 : ℝ) ^ (12 : ℕ)))
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {t x : ℝ} (ht : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ t) (hx : 1 ≤ x)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7 / 8)) :
    (2 * Real.pi / t) * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
      (fun ρ ↦ (t / Real.pi * (1 / ρ.im) + 2) * x ^ (ρ.re - 1)) ≤
      x ^ (-(1 : ℝ) / 4) * CH2.v7.spectralBound t + Real.log x *
        (∫ σ in (3 / 4 : ℝ)..(7 / 8 : ℝ), x ^ (σ - 1) * finiteDensityWeight σ t) := by
  classical
  have hp := Real.pi_pos
  have ht0 : 0 < t := by norm_num at ht; linarith
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t) le_rfl
  set S := hfin.toFinset with hS
  set w : ℂ → ℝ := fun ρ ↦ (t / Real.pi * (1 / ρ.im) + 2) *
    (IEANTN.zetaOrder ρ : ℝ) with hw
  set V := IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
    (fun ρ ↦ t / Real.pi * (1 / ρ.im) + 2) with hV
  set R : ℝ → ℝ := fun σ ↦ IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t)
    (fun ρ ↦ t / Real.pi * (1 / ρ.im) + 2) with hR
  have hw0 : ∀ ρ ∈ S, 0 ≤ w ρ := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset hfin).mp hρ
    have hi : 0 < ρ.im := hh.2.1.1
    have hm := CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hh
    dsimp [w]
    positivity
  have hβ : ∀ ρ ∈ S, ρ.re ≤ (7 / 8 : ℝ) := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset hfin).mp hρ
    exact re_le_boundary hqrh hh.2.2 hh.2.1.1
  have hraw := finite_weighted_density_layer S w Complex.re hx
    (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8) hw0 hβ
  have hleft : (∑ ρ ∈ S, w ρ * x ^ (ρ.re - 1)) =
      IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
        (fun ρ ↦ (t / Real.pi * (1 / ρ.im) + 2) * x ^ (ρ.re - 1)) := by
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin]
    apply Finset.sum_congr rfl
    intro ρ _
    dsimp [w]
    ring
  have htotal : (∑ ρ ∈ S, w ρ) = V := by
    rw [hV, CH2Section7Z.zetaZeroesSum_eq_sum hfin]
  have hfilter : ∀ σ : ℝ, (∑ ρ ∈ S, if σ < ρ.re then w ρ else 0) = R σ := by
    intro σ
    exact density_majorant_filter_eq
  simp only [hleft, htotal, hfilter, show (3 / 4 : ℝ) - 1 = -1 / 4 by norm_num] at hraw
  set k := 2 * Real.pi / t with hk
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hR0 : ∀ σ : ℝ, 0 ≤ R σ := by
    intro σ
    rw [← hfilter σ]
    apply Finset.sum_nonneg
    intro ρ hρ
    split_ifs
    · exact hw0 ρ hρ
    · exact le_rfl
  have hQcont := finiteDensityWeight_continuous ht
  have hpow : Continuous (fun σ : ℝ ↦ x ^ (σ - 1)) := by fun_prop (disch := positivity)
  have hI : k * (∫ σ in (3 / 4 : ℝ)..(7 / 8 : ℝ), x ^ (σ - 1) * R σ) ≤
      ∫ σ in (3 / 4 : ℝ)..(7 / 8 : ℝ), x ^ (σ - 1) * finiteDensityWeight σ t := by
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8),
      intervalIntegral.integral_of_le (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)]
    apply integral_mono_of_nonneg
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall (fun σ _ ↦
        mul_nonneg hk0 (mul_nonneg (Real.rpow_nonneg hx0.le _) (hR0 σ))))
    · exact ((hpow.mul hQcont).continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    · apply (ae_restrict_iff' measurableSet_Ioc).mpr
      filter_upwards [] with σ hσ
      have hh := density_ordinate_majorant_le hFKS hRH hσ.1.le hσ.2 ht
      change k * R σ ≤ finiteDensityWeight σ t at hh
      calc k * (x ^ (σ - 1) * R σ) = x ^ (σ - 1) * (k * R σ) := by ring
        _ ≤ x ^ (σ - 1) * finiteDensityWeight σ t :=
          mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hx0.le _)
  have hBase : k * V ≤ CH2.v7.spectralBound t := by
    have hh := mul_le_mul_of_nonneg_left (ordinate_majorant_sum_le hrvm hsmall hlow
      (by norm_num at ht; linarith : 1000 ≤ t)) hk0
    change k * V ≤ k * (CH2.v7.spectralBound t * (t / (2 * Real.pi))) at hh
    have heq : k * (CH2.v7.spectralBound t * (t / (2 * Real.pi))) =
        CH2.v7.spectralBound t := by dsimp [k]; field_simp
    rwa [heq] at hh
  have hb := mul_le_mul_of_nonneg_left hBase (Real.rpow_nonneg hx0.le (-(1 : ℝ) / 4))
  have hi := mul_le_mul_of_nonneg_left hI hlog
  have hh := mul_le_mul_of_nonneg_left hraw hk0
  change k * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
    (fun ρ ↦ (t / Real.pi * (1 / ρ.im) + 2) * x ^ (ρ.re - 1)) ≤ _
  nlinarith

end CH2QRH
