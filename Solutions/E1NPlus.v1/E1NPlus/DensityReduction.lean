/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.Common
import E1NPlus.Profile
import E1NPlus.LowCDF
import E1NPlus.Ray
import E1NPlus.LogDomain
import E1FrozenN.Interval.DensityReduction

namespace E1NPlus
open Real Set MeasureTheory
set_option maxHeartbeats 0

theorem subset_rvm_count_sharp (hrvm : ZeroCount.v1.rvm_error_bound)
    (S : Finset ℂ) {V t : ℝ}
    (hS : ∀ rho ∈ S, rho ∈ WinnerDirectKernel.positiveZeros V)
    (ht : 1000 ≤ t) :
    (∑ rho ∈ S, if rho.im ≤ t then (IEANTN.zetaOrder rho : ℝ) else 0) ≤
      t*Real.log t/(2*Real.pi) := by
  classical
  apply le_trans ?_ (rvm_count_sharp hrvm ht)
  rw [ZeroCount.v1.zetaNClosed,
    CH2Section7Z.zetaZeroesSum_eq_sum
      (CH2Section7Z.finite_zeros_Ioc (a:=0) (b:=t) le_rfl)]
  simp only [one_mul]
  rw [←Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hr
    obtain ⟨hmem,hcut⟩ := Finset.mem_filter.mp hr
    have hm := WinnerDirectKernel.positive_mem (hS rho hmem)
    exact (Set.Finite.mem_toFinset _).mpr ⟨trivial,⟨hm.2.1.1,hcut⟩,hm.2.2⟩
  · intro rho hr _
    have hm := (Set.Finite.mem_toFinset _).mp hr
    exact CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hm


private theorem profile_height_ge_verified : (3 : ℝ) * 10 ^ (12 : ℕ) ≤ profileHeight := by
  have he : (1 : ℝ) ≤ exp 4 := one_le_exp (by norm_num)
  unfold profileHeight
  nlinarith

/-- The frozen profile controls the actual finite filtered zero count. The
closed-height source theorem is consumed, not assumed as a new CDF oracle. -/
theorem subset_profile_count
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8)) (S : Finset ℂ)
    {V s t : ℝ}
    (hS : ∀ ρ ∈ S, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 V))
    (hreal : ∀ ρ ∈ S, s < ρ.re)
    (hs : (3/4 : ℝ) ≤ s) (hs' : s ≤ 7/8) (ht : profileHeight ≤ t) :
    (∑ ρ ∈ S, if ρ.im ≤ t then (IEANTN.zetaOrder ρ : ℝ) else 0) ≤
      densityMajorant s t := by
  classical
  let Q := (CH2QRH.finite_zero_rectangle (Ioo s 1) (T := t)).toFinset
  have hsub : S.filter (fun ρ ↦ ρ.im ≤ t) ⊆ Q := by
    intro ρ hρ
    obtain ⟨hρS, himt⟩ := Finset.mem_filter.mp hρ
    have ha := hS ρ hρS
    have hb := CH2QRH.re_le_boundary hQRH ha.2.2 ha.2.1.1
    apply (Set.Finite.mem_toFinset
      (CH2QRH.finite_zero_rectangle (Ioo s 1) (T := t))).mpr
    exact ⟨⟨hreal ρ hρS, by linarith⟩, ⟨ha.2.1.1, himt⟩, ha.2.2⟩
  have hnonneg : ∀ ρ ∈ Q, 0 ≤ (IEANTN.zetaOrder ρ : ℝ) := by
    intro ρ hρ
    have ha := (Set.Finite.mem_toFinset
      (CH2QRH.finite_zero_rectangle (Ioo s 1) (T := t))).mp hρ
    exact CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self
      ⟨trivial, ha.2.1, ha.2.2⟩
  calc
    _ = ∑ ρ ∈ S.filter (fun ρ ↦ ρ.im ≤ t), (IEANTN.zetaOrder ρ : ℝ) := by
      rw [Finset.sum_filter]
    _ ≤ ∑ ρ ∈ Q, (IEANTN.zetaOrder ρ : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ _ ↦ hnonneg ρ hρ)
    _ = IEANTN.zetaZeroesSum (Ioo s 1) (Ioc 0 t) (fun _ ↦ (1 : ℝ)) := by
      rw [CH2QRH.rectangle_sum_eq (CH2QRH.finite_zero_rectangle (Ioo s 1) (T := t))]
      simp only [one_mul, Q]
    _ ≤ _ := by
      exact Profile.source_count_closed h hRH hs hs' ht

theorem clipped_density_weight_le_moment
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8)) (S : Finset ℂ)
    {U V s : ℝ} (hU : profileHeight ≤ U) (hUV : U ≤ V)
    (hS : ∀ ρ ∈ S, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 V))
    (hs : (3/4 : ℝ) ≤ s) (hs' : s ≤ 7/8) :
    (∑ ρ ∈ S, if s < ρ.re then
      (IEANTN.zetaOrder ρ : ℝ) / max U ρ.im else 0) ≤ moment s U := by
  classical
  have hU1 : 1 < U := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3 * 10 ^ (12 : ℕ))
    (profile_height_ge_verified.trans hU)
  let Q := S.filter (fun ρ ↦ s < ρ.re)
  have hQS : ∀ ρ ∈ Q, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 V) :=
    fun ρ hρ ↦ hS ρ (Finset.mem_filter.mp hρ).1
  have hQR : ∀ ρ ∈ Q, s < ρ.re := fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2
  have hQV : ∀ ρ ∈ Q, ρ.im ≤ V := fun ρ hρ ↦ (hQS ρ hρ).2.1.2
  have hF : ContinuousOn (densityMajorant s) (uIcc U V) := by
    intro t ht
    rw [uIcc_of_le hUV] at ht
    have ht1 : 1 < t := hU1.trans_le ht.1
    have ht0 : 0 < t := by linarith
    have hl : 0 < log t := log_pos ht1
    have hid : ContinuousAt (fun t : ℝ ↦ t) t := continuousAt_id
    have hlog : ContinuousAt (fun t : ℝ ↦ log t) t := hid.log ht0.ne'
    exact (((hid.rpow_const (by left; exact ht0.ne')).const_mul (coeff s)).mul
      (hlog.rpow_const (by left; exact hl.ne')) |>.add
      ((hlog.pow 2).const_mul 6)).continuousWithinAt
  have hcount : ∀ t ∈ Icc U V,
      (∑ ρ ∈ Q, if ρ.im ≤ t then (IEANTN.zetaOrder ρ : ℝ) else 0) ≤
        densityMajorant s t := by
    intro t ht
    exact subset_profile_count h hRH hQRH Q hQS hQR hs hs' (hU.trans ht.1)
  have hb := E1FrozenN.Interval.finite_clipped_reciprocal_majorant Q Complex.im
    (fun ρ ↦ (IEANTN.zetaOrder ρ : ℝ)) (by linarith) hUV hQV
    (densityMajorant s) hF hcount
  have hm := hb.trans (moment_bound hU1 hUV hs hs')
  simpa only [Q, Finset.sum_filter] using hm

/-- The exact actual-zero layer bound with the old proved height profile. -/
theorem clipped_density_layer_bound
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8)) (S : Finset ℂ)
    {U V x : ℝ} (hU : profileHeight ≤ U) (hUV : U ≤ V) (hx : 1 ≤ x)
    (hS : ∀ ρ ∈ S, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 V))
    (hcount : ∀ t ∈ Icc U V,
      (∑ ρ ∈ S, if ρ.im ≤ t then (IEANTN.zetaOrder ρ : ℝ) else 0) ≤ t * log t/(2*Real.pi)) :
    (∑ ρ ∈ S, ((IEANTN.zetaOrder ρ : ℝ) / max U ρ.im) * x ^ (ρ.re - 1)) ≤
      x ^ (-(1 : ℝ)/4) * ((log V+(log V^2-log U^2)/2)/(2*Real.pi)) + log x *
        (∫ s in (3/4 : ℝ)..(7/8 : ℝ), x ^ (s - 1) * moment s U) := by
  classical
  have hU1 : 1 < U := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3 * 10 ^ (12 : ℕ))
    (profile_height_ge_verified.trans hU)
  have hUpos : 0 < U := by linarith
  have hxpos : 0 < x := by linarith
  let w : ℂ → ℝ := fun ρ ↦ (IEANTN.zetaOrder ρ : ℝ) / max U ρ.im
  have hw : ∀ ρ ∈ S, 0 ≤ w ρ := by
    intro ρ hρ
    exact div_nonneg (CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self (hS ρ hρ))
      (hUpos.le.trans (le_max_left U ρ.im))
  have hb : ∀ ρ ∈ S, ρ.re ≤ (7/8 : ℝ) := by
    intro ρ hρ
    have ha := hS ρ hρ
    exact CH2QRH.re_le_boundary hQRH ha.2.2 ha.2.1.1
  have hlayer := CH2QRH.finite_weighted_density_layer S w Complex.re hx
    (by norm_num : (3/4 : ℝ) ≤ 7/8) hw hb
  have htotal := finite_clipped_sharp_majorant S Complex.im (fun ρ↦(IEANTN.zetaOrder ρ:ℝ)) hUpos hUV
    (fun ρ hρ ↦ (hS ρ hρ).2.1.2) hcount
  have hpow : Continuous (fun s : ℝ ↦ x ^ (s - 1)) := by
    fun_prop (disch := positivity)
  have hIntUpper : IntegrableOn (fun s : ℝ ↦ x ^ (s - 1) * moment s U)
      (Ioc (3/4 : ℝ) (7/8 : ℝ)) :=
    ((hpow.continuousOn.mul (moment_continuousOn hU1)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hInt : (∫ s in (3/4 : ℝ)..(7/8 : ℝ),
      x ^ (s - 1) * (∑ ρ ∈ S, if s < ρ.re then w ρ else 0)) ≤
      ∫ s in (3/4 : ℝ)..(7/8 : ℝ), x ^ (s - 1) * moment s U := by
    rw [intervalIntegral.integral_of_le (by norm_num : (3/4 : ℝ) ≤ 7/8),
      intervalIntegral.integral_of_le (by norm_num : (3/4 : ℝ) ≤ 7/8)]
    apply integral_mono_of_nonneg
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall (fun s _ ↦ mul_nonneg
          (Real.rpow_nonneg hxpos.le _) (Finset.sum_nonneg (fun ρ hρ ↦ by
            split_ifs
            · exact hw ρ hρ
            · exact le_rfl))))
    · exact hIntUpper
    · apply (ae_restrict_iff' measurableSet_Ioc).mpr
      filter_upwards [] with s hs
      exact mul_le_mul_of_nonneg_left
        (clipped_density_weight_le_moment h hRH hQRH S hU hUV hS hs.1.le hs.2)
        (Real.rpow_nonneg hxpos.le _)
  change (∑ ρ ∈ S, w ρ * x ^ (ρ.re - 1)) ≤ _
  have hbase := mul_le_mul_of_nonneg_left htotal (Real.rpow_nonneg hxpos.le (-(1 : ℝ)/4))
  have hhigh := mul_le_mul_of_nonneg_left hInt (Real.log_nonneg hx)
  simp only [show (3/4 : ℝ) - 1 = -1/4 by norm_num] at hlayer
  exact hlayer.trans (add_le_add hbase hhigh)

/-- Final normalization uses actual RVM counts and the proved profile CDF,
retaining every zero below the clipping height with weight 1/U. -/
theorem clipped_density_layer_exp_bound
    (hrvm : ZeroCount.v1.rvm_error_bound)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8)) (S : Finset ℂ)
    {L : ℝ} (hL : 330 ≤ L)
    (hS : ∀ ρ ∈ S, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 (V L))) :
    2 * U L * (∑ ρ ∈ S, ((IEANTN.zetaOrder ρ : ℝ) / max (U L) ρ.im) *
      exp (-(1 - ρ.re) * L)) ≤ low L + high L := by
  have hU := U_ge_profileHeight hL
  have hUV := U_le_V hL
  have hSF : ∀ ρ ∈ S, ρ ∈ WinnerDirectKernel.positiveZeros (V L) := by
    intro ρ hρ
    exact (Set.Finite.mem_toFinset _).mpr (hS ρ hρ)
  have hcount : ∀ t ∈ Icc (U L) (V L),
      (∑ ρ ∈ S, if ρ.im ≤ t then (IEANTN.zetaOrder ρ : ℝ) else 0) ≤ t * log t/(2*Real.pi) := by
    intro t ht
    have hh:3*(10:ℝ)^12 ≤ t:=(U_ge_height hL).trans ht.1
    exact subset_rvm_count_sharp hrvm S hSF (by linarith)
  have hx : 1 ≤ exp L := Real.one_le_exp (by linarith)
  have hb := clipped_density_layer_bound h hRH hQRH S hU hUV hx hS hcount
  simp_rw [Real.rpow_def_of_pos (exp_pos L), Real.log_exp] at hb
  have he : ∀ s : ℝ, L * (s - 1) = -(1 - s) * L := by intro s; ring
  simp_rw [he] at hb
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * U L by unfold U k; positivity)
  have hbase : 2 * U L * exp (L * (-(1 : ℝ)/4)) = 2 * k * exp (-L/25) := by
    unfold U
    calc
      _ = 2 * k * (exp (eta * L) * exp (L * (-(1 : ℝ)/4))) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [eta]; ring
  rw [mul_add, ← mul_assoc, hbase,log_U] at hm
  convert! hm using 1
  unfold low high
  field_simp
  <;> ring

end E1NPlus

#print axioms E1NPlus.subset_profile_count
#print axioms E1NPlus.clipped_density_layer_exp_bound
