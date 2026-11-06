/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.ClippedCDF
import DirectIntervalA.Common
import DirectIntervalA.LogDomain

open Real Set MeasureTheory

namespace DirectIntervalA

/-- The minimum in the interval explicit formula is bounded by one clipped
reciprocal weight when `delta * U = K` and `2 + delta ≤ K`. -/
theorem min_le_clipped_reciprocal {δ K U γ : ℝ}
    (hU : 0 < U) (hγ : 0 < γ) (hδU : δ * U = K) (hK : 2 + δ ≤ K) :
    min δ ((2 + δ) / γ) ≤ K / max U γ := by
  rcases le_total γ U with h | h
  · rw [max_eq_left h]
    calc
      _ ≤ δ := min_le_left _ _
      _ = K / U := (eq_div_iff hU.ne').mpr hδU
  · rw [max_eq_right h]
    exact (min_le_right _ _).trans (div_le_div_of_nonneg_right hK hγ.le)

/-- A finite subset of actual positive zeros has no larger filtered count than
the published FKS count, with its closed height supplied by continuity. -/
theorem subset_fks_count (hFKS : FKS.v3.density_0618)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7 / 8)) (S : Finset ℂ)
    {V s t : ℝ}
    (hS : ∀ ρ ∈ S, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 V))
    (hreal : ∀ ρ ∈ S, s < ρ.re)
    (hs : (3 / 4 : ℝ) ≤ s) (hs' : s ≤ 7 / 8)
    (ht : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ t) :
    (∑ ρ ∈ S, if ρ.im ≤ t then (IEANTN.zetaOrder ρ : ℝ) else 0) ≤
      CH2QRH.fksDensityMajorant s t := by
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
    _ ≤ _ := CH2QRH.fks_density_closed hFKS hs hs' ht

/-- Clipped reciprocal weights are bounded by the actual FKS moment at `U`.
Zeros below `U` remain present, each with reciprocal weight `1/U`. -/
theorem clipped_density_weight_le_moment (hFKS : FKS.v3.density_0618)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7 / 8)) (S : Finset ℂ)
    {U V s : ℝ} (hU : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ U) (hUV : U ≤ V)
    (hS : ∀ ρ ∈ S, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 V))
    (hs : (3 / 4 : ℝ) ≤ s) (hs' : s ≤ 7 / 8) :
    (∑ ρ ∈ S, if s < ρ.re then
      (IEANTN.zetaOrder ρ : ℝ) / max U ρ.im else 0) ≤ moment s U := by
  classical
  have hU1 : 1 < U := lt_of_lt_of_le (by norm_num) hU
  let Q := S.filter (fun ρ ↦ s < ρ.re)
  have hQS : ∀ ρ ∈ Q, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 V) :=
    fun ρ hρ ↦ hS ρ (Finset.mem_filter.mp hρ).1
  have hQR : ∀ ρ ∈ Q, s < ρ.re := fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2
  have hQV : ∀ ρ ∈ Q, ρ.im ≤ V := fun ρ hρ ↦ (hQS ρ hρ).2.1.2
  have hF : ContinuousOn (CH2QRH.fksDensityMajorant s) (uIcc U V) := by
    intro t ht
    rw [uIcc_of_le hUV] at ht
    exact (CH2QRH.fksDensityMajorant_continuousAt (hU1.trans_le ht.1)).continuousWithinAt
  have hcount : ∀ t ∈ Icc U V,
      (∑ ρ ∈ Q, if ρ.im ≤ t then (IEANTN.zetaOrder ρ : ℝ) else 0) ≤
        CH2QRH.fksDensityMajorant s t := by
    intro t ht
    exact subset_fks_count hFKS hQRH Q hQS hQR hs hs' (hU.trans ht.1)
  have hb := finite_clipped_reciprocal_majorant Q Complex.im
    (fun ρ ↦ (IEANTN.zetaOrder ρ : ℝ)) (by linarith) hUV hQV
    (CH2QRH.fksDensityMajorant s) hF hcount
  have hm := hb.trans (moment_bound hU1 hUV hs hs')
  simpa only [Q, Finset.sum_filter] using hm

/-- The elementary logarithmic count has an exact finite reciprocal moment. -/
theorem log_count_moment_bound {U V : ℝ} (hU : 0 < U) (hUV : U ≤ V) :
    (V * log V) / V + (∫ t in U..V, (t * log t) / t ^ 2) ≤
      log V + log V ^ (2 : ℕ) / 2 := by
  have hV : 0 < V := hU.trans_le hUV
  have hd : ∀ t ∈ uIcc U V,
      HasDerivAt (fun z : ℝ ↦ log z ^ (2 : ℕ) / 2) (log t / t) t := by
    intro t ht
    rw [uIcc_of_le hUV] at ht
    have ht0 : t ≠ 0 := (hU.trans_le ht.1).ne'
    convert! ((Real.hasDerivAt_log ht0).pow 2).div_const 2 using 1 <;> norm_num <;> ring
  have hi : IntervalIntegrable (fun t : ℝ ↦ log t / t) volume U V := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hUV] at ht
    have ht0 : t ≠ 0 := (hU.trans_le ht.1).ne'
    exact ((Real.continuousAt_log ht0).div continuousAt_id ht0).continuousWithinAt
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have he : (∫ t in U..V, (t * log t) / t ^ 2) = ∫ t in U..V, log t / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hUV] at ht
    have ht0 : t ≠ 0 := (hU.trans_le ht.1).ne'
    change (t * log t) / t ^ 2 = log t / t
    field_simp
  rw [he, hI, mul_div_cancel_left₀ (log V) hV.ne']
  nlinarith [sq_nonneg (log U)]

/-- A generic total-count input is kept explicit so the RVM-only count bound can
be supplied independently without adding finite-RH or low-zero premises. -/
theorem clipped_total_weight_le (S : Finset ℂ) {U V : ℝ}
    (hU : 0 < U) (hUV : U ≤ V)
    (hSV : ∀ ρ ∈ S, ρ.im ≤ V)
    (hcount : ∀ t ∈ Icc U V,
      (∑ ρ ∈ S, if ρ.im ≤ t then (IEANTN.zetaOrder ρ : ℝ) else 0) ≤ t * log t) :
    (∑ ρ ∈ S, (IEANTN.zetaOrder ρ : ℝ) / max U ρ.im) ≤
      log V + log V ^ (2 : ℕ) / 2 := by
  have hF : ContinuousOn (fun t : ℝ ↦ t * log t) (uIcc U V) := by
    intro t ht
    rw [uIcc_of_le hUV] at ht
    have ht0 : t ≠ 0 := (hU.trans_le ht.1).ne'
    exact (continuousAt_id.mul (Real.continuousAt_log ht0)).continuousWithinAt
  exact (finite_clipped_reciprocal_majorant S Complex.im
    (fun ρ ↦ (IEANTN.zetaOrder ρ : ℝ)) hU hUV hSV (fun t ↦ t * log t) hF hcount).trans
      (log_count_moment_bound hU hUV)

theorem moment_continuousOn {U : ℝ} (hU : 1 < U) :
    ContinuousOn (fun s : ℝ ↦ moment s U) (Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) := by
  intro s hs
  have hUpos : 0 < U := by linarith
  have hlpos : 0 < log U := Real.log_pos hU
  have hapos : 0 < 1 - 8 * (1 - s) / 3 := by linarith [hs.1]
  dsimp [moment, CH2QRH.densityMomentMain]
  fun_prop (disch := positivity)

/-- A finite set of actual positive zeros is controlled by a low RVM count
moment and the high FKS density moment. No finite RH input is used. -/
theorem clipped_density_layer_bound (hFKS : FKS.v3.density_0618)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7 / 8)) (S : Finset ℂ)
    {U V x : ℝ} (hU : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ U) (hUV : U ≤ V) (hx : 1 ≤ x)
    (hS : ∀ ρ ∈ S, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 V))
    (hcount : ∀ t ∈ Icc U V,
      (∑ ρ ∈ S, if ρ.im ≤ t then (IEANTN.zetaOrder ρ : ℝ) else 0) ≤ t * log t) :
    (∑ ρ ∈ S, ((IEANTN.zetaOrder ρ : ℝ) / max U ρ.im) * x ^ (ρ.re - 1)) ≤
      x ^ (-(1 : ℝ) / 4) * (log V + log V ^ (2 : ℕ) / 2) + log x *
        (∫ s in (3 / 4 : ℝ)..(7 / 8 : ℝ), x ^ (s - 1) * moment s U) := by
  classical
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hU1 : 1 < U := lt_of_lt_of_le (by norm_num) hU
  have hxpos : 0 < x := by linarith
  let w : ℂ → ℝ := fun ρ ↦ (IEANTN.zetaOrder ρ : ℝ) / max U ρ.im
  have hw : ∀ ρ ∈ S, 0 ≤ w ρ := by
    intro ρ hρ
    have ha := hS ρ hρ
    exact div_nonneg (CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self ha)
      (hUpos.le.trans (le_max_left U ρ.im))
  have hb : ∀ ρ ∈ S, ρ.re ≤ (7 / 8 : ℝ) := by
    intro ρ hρ
    have ha := hS ρ hρ
    exact CH2QRH.re_le_boundary hQRH ha.2.2 ha.2.1.1
  have hlayer := CH2QRH.finite_weighted_density_layer S w Complex.re hx
    (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8) hw hb
  have htotal := clipped_total_weight_le S hUpos hUV
    (fun ρ hρ ↦ (hS ρ hρ).2.1.2) hcount
  have hpow : Continuous (fun s : ℝ ↦ x ^ (s - 1)) := by
    fun_prop (disch := positivity)
  have hIntUpper : IntegrableOn (fun s : ℝ ↦ x ^ (s - 1) * moment s U)
      (Ioc (3 / 4 : ℝ) (7 / 8 : ℝ)) :=
    ((hpow.continuousOn.mul (moment_continuousOn hU1)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hInt : (∫ s in (3 / 4 : ℝ)..(7 / 8 : ℝ),
      x ^ (s - 1) * (∑ ρ ∈ S, if s < ρ.re then w ρ else 0)) ≤
      ∫ s in (3 / 4 : ℝ)..(7 / 8 : ℝ), x ^ (s - 1) * moment s U := by
    rw [intervalIntegral.integral_of_le (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8),
      intervalIntegral.integral_of_le (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)]
    apply integral_mono_of_nonneg
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall (fun s _ ↦
        mul_nonneg (Real.rpow_nonneg hxpos.le _) (Finset.sum_nonneg (fun ρ hρ ↦ by
          split_ifs
          · exact hw ρ hρ
          · exact le_rfl))))
    · exact hIntUpper
    · apply (ae_restrict_iff' measurableSet_Ioc).mpr
      filter_upwards [] with s hs
      exact mul_le_mul_of_nonneg_left
        (clipped_density_weight_le_moment hFKS hQRH S hU hUV hS hs.1.le hs.2)
        (Real.rpow_nonneg hxpos.le _)
  change (∑ ρ ∈ S, w ρ * x ^ (ρ.re - 1)) ≤ _
  have hbase := mul_le_mul_of_nonneg_left htotal (Real.rpow_nonneg hxpos.le (-(1 : ℝ) / 4))
  have hhigh := mul_le_mul_of_nonneg_left hInt (Real.log_nonneg hx)
  simp only [show (3 / 4 : ℝ) - 1 = -1 / 4 by norm_num] at hlayer
  exact hlayer.trans (add_le_add hbase hhigh)

/-- The actual-zero layer bound in the logarithmic normalization used by the
interval application. RVM supplies the total count and FKS supplies the high part. -/
theorem clipped_density_layer_exp_bound (hrvm : ZeroCount.v1.rvm_error_bound)
    (hFKS : FKS.v3.density_0618) (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7 / 8))
    (S : Finset ℂ) {L : ℝ} (hL : 330 ≤ L)
    (hS : ∀ ρ ∈ S, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 (V L))) :
    2 * U L * (∑ ρ ∈ S, ((IEANTN.zetaOrder ρ : ℝ) / max (U L) ρ.im) *
      exp (-(1 - ρ.re) * L)) ≤ low L + high L := by
  have hU := U_ge_height hL
  have hUV := U_le_V hL
  have hSF : ∀ ρ ∈ S, ρ ∈ WinnerDirectKernel.positiveZeros (V L) := by
    intro ρ hρ
    exact (Set.Finite.mem_toFinset _).mpr (hS ρ hρ)
  have hcount : ∀ t ∈ Icc (U L) (V L),
      (∑ ρ ∈ S, if ρ.im ≤ t then (IEANTN.zetaOrder ρ : ℝ) else 0) ≤ t * log t := by
    intro t ht
    exact subset_rvm_count hrvm S hSF (hU.trans ht.1)
  have hx : 1 ≤ exp L := Real.one_le_exp (by linarith)
  have hb := clipped_density_layer_bound hFKS hQRH S hU hUV hx hS hcount
  simp_rw [Real.rpow_def_of_pos (exp_pos L), Real.log_exp] at hb
  have he : ∀ s : ℝ, L * (s - 1) = -(1 - s) * L := by intro s; ring
  simp_rw [he] at hb
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * U L by
    unfold U; positivity)
  have hbase : 2 * U L * exp (L * (-(1 : ℝ) / 4)) =
      2 * k * exp (-L / 20) := by
    unfold U
    calc
      _ = 2 * k * (exp (L / 5) * exp (L * (-(1 : ℝ) / 4))) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  rw [mul_add, ← mul_assoc, hbase] at hm
  convert! hm using 1
  unfold low high U
  ring

end DirectIntervalA

#print axioms DirectIntervalA.clipped_density_layer_bound
#print axioms DirectIntervalA.clipped_density_layer_exp_bound
#print axioms DirectIntervalA.min_le_clipped_reciprocal
