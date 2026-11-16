/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex), adapted from Terence Tao
-/
import Section81Titch

/-! A generalization of the existing CH2 local logarithmic-derivative estimate.
The old proof uses finite-height RH only to bound the inner sum at Re s = 3/2.
Here every zero has Re rho < 1, giving the weaker bound 2 per inner summand. -/
open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2Section81

set_option maxHeartbeats 2000000 in
theorem titch96A_no_RH (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    {σ t : ℝ} (ht : 1000 ≤ t) (hσ0 : -1 / 2 ≤ σ) (hσ1 : σ ≤ 1)
    (hs : riemannZeta ((σ : ℂ) + t * I) ≠ 0) :
    ‖deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)
        - IEANTN.zetaZeroesSum Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4))
            (fun ρ ↦ 1 / ((σ : ℂ) + t * I - ρ))‖
      ≤ (4 * (3 / 2 - σ) + 1 / 4) / Real.pi * Real.log (t / (2 * Real.pi))
        + (32 * (3 / 2 - σ) - 1) * (2 / 5 * Real.log t + 4) + 1.5053 + 0.016
        + ((2 / 5 + 1 / (4 * Real.pi)) * Real.log t + 4.001) := by
  classical
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  set s : ℂ := (σ : ℂ) + t * I with hs_def
  set w : ℂ := ((3 / 2 : ℝ) : ℂ) + t * I with hw_def
  have hsre : s.re = σ := by simp [hs_def]
  have hsim : s.im = t := by simp [hs_def]
  have hwre : w.re = 3 / 2 := by simp [hw_def]
  have hwim : w.im = t := by simp [hw_def]
  have hws : w - s = ((3 / 2 - σ : ℝ) : ℂ) := by rw [hs_def, hw_def]; push_cast; ring
  have hk0 : (0 : ℝ) ≤ 3 / 2 - σ := by linarith
  have hs1 : s ≠ 1 := fun h ↦ by
    have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hw1 : w ≠ 1 := fun h ↦ by
    have := congrArg Complex.im h; rw [hwim] at this; simp at this; linarith
  have hwz : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hwre]; norm_num)
  have hS := hH s w hs1 hw1 hs hwz
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := t - 1 / 4) (b := t + 1 / 4) (by linarith)
  have hmem : ∀ ρ ∈ hfin.toFinset, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)) :=
    fun ρ hρ ↦ (Set.Finite.mem_toFinset hfin).mp hρ
  have hI₀Z : ∀ ρ ∈ hfin.toFinset, ρ ∈ IEANTN.zetaZeroesIn (Set.Ioo (0 : ℝ) 1) Set.univ := by
    intro ρ hρ
    have hρ' := hmem ρ hρ
    have him : ρ.im ≠ 0 := by have := hρ'.2.1.1; intro h; rw [h] at this; linarith
    exact ⟨re_pos_of_zero hρ'.2.2 him, trivial, hρ'.2.2⟩
  have hm0 : ∀ ρ ∈ hfin.toFinset, (0 : ℝ) ≤ IEANTN.zetaOrder ρ := fun ρ hρ ↦
    CH2Section7Z.zetaOrder_nonneg_of_mem (fun x hx ↦ show (0 : ℝ) < x by linarith [hx.1]) (hmem ρ hρ)
  set Z := IEANTN.zetaZeroesIn (Set.Ioo (0 : ℝ) 1) Set.univ with hZ
  set I₀ : Finset Z := hfin.toFinset.subtype (· ∈ Z) with hI₀
  set f : Z → ℂ := fun ρ ↦ (1 / (s - (ρ : ℂ)) - 1 / (w - (ρ : ℂ))) * (IEANTN.zetaOrder (ρ : ℂ) : ℂ)
    with hf
  have hsumI : ∑ ρ ∈ I₀, f ρ = ∑ ρ ∈ hfin.toFinset, 1 / (s - ρ) * (IEANTN.zetaOrder ρ : ℂ)
      - ∑ ρ ∈ hfin.toFinset, 1 / (w - ρ) * (IEANTN.zetaOrder ρ : ℂ) := by
    rw [← Finset.sum_sub_distrib]
    have := Finset.sum_subtype_eq_sum_filter (s := hfin.toFinset) (p := (· ∈ Z))
      (fun ρ : ℂ ↦ (1 / (s - ρ) - 1 / (w - ρ)) * (IEANTN.zetaOrder ρ : ℂ))
    rw [Finset.filter_true_of_mem hI₀Z] at this
    rw [hI₀, hf]; simp only at this ⊢
    rw [this]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  set V : ℂ := deriv riemannZeta s / riemannZeta s - deriv riemannZeta w / riemannZeta w
        + (Complex.digamma (s / 2 + 1) - Complex.digamma (w / 2 + 1)) / 2
        + 1 / (s - 1) - 1 / (w - 1) with hV
  have hout : HasSum (fun x : {x : Z // x ∉ I₀} ↦ f x) (V - ∑ i ∈ I₀, f i) :=
    (Finset.hasSum_compl_iff I₀).mpr (by rw [sub_add_cancel]; exact hS)
  -- the outer sum
  have hA : ‖V - ∑ i ∈ I₀, f i‖ ≤ (3 / 2 - σ) * (4 / Real.pi * Real.log (t / (2 * Real.pi))
        + 16 * (2 / 5 * Real.log t + 4
          + (ZeroCount.v1.zetaNClosed (t - 1 / 4) - ZeroCount.v1.rvmMain (t - 1 / 4))
          - (ZeroCount.v1.zetaNClosed (t + 1 / 4) - ZeroCount.v1.rvmMain (t + 1 / 4))) + 0.004) := by
    refine le_of_tendsto' ((continuous_norm.tendsto _).comp hout) fun F ↦ ?_
    simp only [Function.comp_apply]
    have hpt : ∀ x : {x : Z // x ∉ I₀}, riemannZeta x.1.1 = 0 ∧ x.1.1.im ≠ 0
        ∧ (x.1.1.im ≤ t - 1 / 4 ∨ t + 1 / 4 < x.1.1.im) := by
      intro x
      have hx1 := x.1.2
      have hx2 : x.1.1 ∉ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)) :=
        fun h ↦ x.2 (Finset.mem_subtype.mpr ((Set.Finite.mem_toFinset hfin).mpr h))
      refine ⟨hx1.2.2, im_ne_zero_of_nontrivial hx1, ?_⟩
      by_contra hc
      push Not at hc
      exact hx2 ⟨trivial, ⟨hc.1, hc.2⟩, hx1.2.2⟩
    calc ‖∑ x ∈ F, f x‖ ≤ ∑ x ∈ F, ‖f x‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ F, (3 / 2 - σ) * ((IEANTN.zetaOrder x.1.1 : ℝ)
            * (1 / (t - x.1.1.im) ^ 2)) := Finset.sum_le_sum fun x _ ↦ by
          obtain ⟨hz, him, hpos⟩ := hpt x
          have hre := re_pos_of_zero hz him
          have h1 : x.1.1 ≠ 1 := fun h ↦ by rw [h] at hre; simp at hre
          have hm : (0 : ℝ) ≤ IEANTN.zetaOrder x.1.1 := by
            exact_mod_cast CH2Section6.zetaOrder_nonneg_of_ne_one h1
          have hγ : t - x.1.1.im ≠ 0 := by
            rcases hpos with h | h <;> intro h' <;> linarith
          simp only [hf]
          rw [norm_mul, norm_zetaOrder_cast hm]
          have := norm_inv_sub_inv_le hsim hwim hws hk0 hγ
          calc _ ≤ (3 / 2 - σ) * (1 / (t - x.1.1.im) ^ 2)
                * (IEANTN.zetaOrder x.1.1 : ℝ) := mul_le_mul_of_nonneg_right this hm
            _ = _ := by ring
      _ = (3 / 2 - σ) * ∑ ρ ∈ F.image (fun x : {x : Z // x ∉ I₀} ↦ x.1.1),
            (IEANTN.zetaOrder ρ : ℝ) * (1 / (t - ρ.im) ^ 2) := by
          rw [Finset.mul_sum, Finset.sum_image]
          intro a _ b _ h
          exact Subtype.ext (Subtype.ext h)
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (outer_finset_le hrvm hsmall ht _ ?_) hk0
          intro ρ hρ
          rw [Finset.mem_image] at hρ
          obtain ⟨x, -, rfl⟩ := hρ
          exact hpt x
  -- the inner sum at `w`
  have hB : ‖∑ ρ ∈ hfin.toFinset, 1 / (w - ρ) * (IEANTN.zetaOrder ρ : ℂ)‖
      ≤ 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4))
        (fun _ ↦ (1 : ℝ)) := by
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
    have hρ' := hmem ρ hρ
    have him : ρ.im ≠ 0 := by
      have hp := hρ'.2.1.1
      intro he
      rw [he] at hp
      linarith
    have hre := (re_pos_of_zero hρ'.2.2 him).2
    have hn : (1 / 2 : ℝ) ≤ ‖w - ρ‖ := by
      have hr : (1 / 2 : ℝ) ≤ (w - ρ).re := by
        simp only [Complex.sub_re, hwre]
        linarith
      exact hr.trans (Complex.re_le_norm _)
    have hi : ‖1 / (w - ρ)‖ ≤ 2 := by
      rw [norm_div, norm_one]
      exact (div_le_iff₀ (by linarith : 0 < ‖w - ρ‖)).mpr (by linarith)
    rw [norm_mul, norm_zetaOrder_cast (hm0 ρ hρ)]
    simpa using mul_le_mul_of_nonneg_right hi (hm0 ρ hρ)
  have hBc := inner_count_le hrvm ht
  -- `ζ'/ζ(w)`
  have hC := norm_logDeriv_zeta_le_three_halves hv (w := w) (by rw [hwre])
  -- the digamma difference
  have hD : ‖(Complex.digamma (s / 2 + 1) - Complex.digamma (w / 2 + 1)) / 2‖ ≤ 0.008 / 2 := by
    have hz1re : (s / 2 + 1).re = σ / 2 + 1 := by simp [hsre]
    have hz2re : (w / 2 + 1).re = 3 / 4 + 1 := by simp [hwre]; norm_num
    have hz1im : (s / 2 + 1).im = t / 2 := by simp [hsim]
    have hz2im : (w / 2 + 1).im = t / 2 := by simp [hwim]
    have hdiff : s / 2 + 1 - (w / 2 + 1) = ((-((3 / 2 - σ) / 2) : ℝ) : ℂ) := by
      have : s - w = ((-(3 / 2 - σ) : ℝ) : ℂ) := by
        rw [← neg_sub, hws]; push_cast; ring
      push_cast at this ⊢
      linear_combination this / 2
    have h := norm_digamma_sub_le (z₁ := s / 2 + 1) (z₂ := w / 2 + 1) (by rw [hz1re]; linarith)
      (by rw [hz2re]; norm_num) (by rw [hz1im, hz2im]) (by rw [hz1im]; linarith)
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by linarith), hz1im] at h
    have h2 : (3 / 2 - σ) / 2 * (4 / (t / 2)) ≤ 0.008 := by
      rw [show (3 / 2 - σ) / 2 * (4 / (t / 2)) = 4 * (3 / 2 - σ) / t by field_simp,
        div_le_iff₀ (by linarith)]
      nlinarith
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    linarith
  -- the pole term
  have hE : ‖1 / (s - 1) - 1 / (w - 1)‖ ≤ 0.000002 := by
    have h := norm_inv_sub_inv_le (ρ := 1) hsim hwim hws hk0 (by simp; linarith)
    simp only [Complex.one_im, sub_zero] at h
    have h1 : 1 / t ^ 2 ≤ 0.000001 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h0 : 0 ≤ 1 / t ^ 2 := by positivity
    nlinarith
  -- assembly
  have heq : deriv riemannZeta s / riemannZeta s
      - ∑ ρ ∈ hfin.toFinset, 1 / (s - ρ) * (IEANTN.zetaOrder ρ : ℂ)
      = (V - ∑ i ∈ I₀, f i) - ∑ ρ ∈ hfin.toFinset, 1 / (w - ρ) * (IEANTN.zetaOrder ρ : ℂ)
        + deriv riemannZeta w / riemannZeta w
        - (Complex.digamma (s / 2 + 1) - Complex.digamma (w / 2 + 1)) / 2
        - (1 / (s - 1) - 1 / (w - 1)) := by
    rw [hsumI, hV]; ring
  rw [zetaZeroesSum_eq_sum_C hfin, heq]
  refine (norm_five _ _ _ _ _).trans ?_
  -- the `Q` terms
  have hQm := abs_le.mp (hrvm (t - 1 / 4) (by linarith))
  have hQp := abs_le.mp (hrvm (t + 1 / 4) (by linarith))
  have hlogm : Real.log (t - 1 / 4) ≤ Real.log t := Real.log_le_log (by linarith) (by linarith)
  have hlogp : Real.log (t + 1 / 4) ≤ Real.log t + 0.00025 := by
    have e : Real.log (t + 1 / 4) = Real.log t + Real.log (1 + 1 / (4 * t)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    have h3 := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (4 * t) by positivity)
    have h4 : 1 / (4 * t) ≤ 0.00025 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hQd : (ZeroCount.v1.zetaNClosed (t - 1 / 4) - ZeroCount.v1.rvmMain (t - 1 / 4))
      - (ZeroCount.v1.zetaNClosed (t + 1 / 4) - ZeroCount.v1.rvmMain (t + 1 / 4))
      ≤ 2 / 5 * Real.log t + 4 + 0.0001 := by linarith
  have hQd' := mul_le_mul_of_nonneg_left hQd (show (0 : ℝ) ≤ 16 * (3 / 2 - σ) - 1 by linarith)
  have hL0 : 0 ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four])
  have hQdrev :
      (ZeroCount.v1.zetaNClosed (t + 1 / 4) - ZeroCount.v1.rvmMain (t + 1 / 4))
        - (ZeroCount.v1.zetaNClosed (t - 1 / 4) - ZeroCount.v1.rvmMain (t - 1 / 4))
        ≤ 2 / 5 * Real.log t + 4 + 0.0001 := by
    linarith
  have hlogratio : Real.log (t / (2 * Real.pi)) ≤ Real.log t :=
    Real.log_le_log (by positivity) (div_le_self (by linarith) (by linarith))
  have hN : IEANTN.zetaZeroesSum Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4))
      (fun _ ↦ (1 : ℝ)) ≤ (2 / 5 + 1 / (4 * Real.pi)) * Real.log t + 4.001 := by
    have hlogmul := mul_le_mul_of_nonneg_left hlogratio
      (show 0 ≤ 1 / (4 * Real.pi) by positivity)
    nlinarith
  have hB' : ‖∑ ρ ∈ hfin.toFinset, 1 / (w - ρ) * (IEANTN.zetaOrder ρ : ℂ)‖
      ≤ IEANTN.zetaZeroesSum Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4))
          (fun _ ↦ (1 : ℝ)) + ((2 / 5 + 1 / (4 * Real.pi)) * Real.log t + 4.001) := by
    linarith
  have e1 : 1 / (4 * Real.pi) * Real.log (t / (2 * Real.pi))
      = (1 / 4) / Real.pi * Real.log (t / (2 * Real.pi)) := by field_simp
  have e2 : (4 * (3 / 2 - σ) + 1 / 4) / Real.pi * Real.log (t / (2 * Real.pi))
      = (3 / 2 - σ) * (4 / Real.pi * Real.log (t / (2 * Real.pi)))
        + (1 / 4) / Real.pi * Real.log (t / (2 * Real.pi)) := by field_simp
  rw [e2]
  nlinarith


end CH2QRH
