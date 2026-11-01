/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityPartialSum
import IEANTN.Nodes.FKS.v3.Conclusions

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- The exact FKS density majorant, kept separate from the formalized summation machinery. -/
noncomputable def fksDensityMajorant (σ T : ℝ) : ℝ :=
  9.795 * T ^ (8 * (1 - σ) / 3) * (Real.log T) ^ (5 - 2 * σ) + 4.465 * Real.log T ^ 2

/-- Finite support for an arbitrary real-part restriction at positive height. -/
theorem finite_zero_rectangle (I : Set ℝ) {T : ℝ} :
    (IEANTN.zetaZeroesIn I (Set.Ioc 0 T)).Finite := by
  exact (CH2Section7Z.finite_zeros_Ioc (a := 0) (b := T) le_rfl).subset
    (fun ρ hρ ↦ ⟨trivial, hρ.2.1, hρ.2.2⟩)

/-- Expand a rectangle sum only after its finite support has been established. -/
theorem rectangle_sum_eq {I J : Set ℝ} (hfin : (IEANTN.zetaZeroesIn I J).Finite)
    (f : ℂ → ℝ) :
    IEANTN.zetaZeroesSum I J f = ∑ ρ ∈ hfin.toFinset, f ρ * (IEANTN.zetaOrder ρ : ℝ) := by
  unfold IEANTN.zetaZeroesSum
  rw [tsum_subtype (IEANTN.zetaZeroesIn I J) (fun ρ ↦ f ρ * (IEANTN.zetaOrder ρ : ℝ)),
    tsum_eq_sum (s := hfin.toFinset)]
  · exact Finset.sum_congr rfl fun ρ hρ ↦
      Set.indicator_of_mem ((Set.Finite.mem_toFinset hfin).mp hρ) _
  · intro ρ hρ
    exact Set.indicator_of_notMem (fun h ↦ hρ ((Set.Finite.mem_toFinset hfin).mpr h)) _

/-- A closed ordinate cutoff is contained in every slightly larger strict cutoff. -/
theorem density_closed_le_open {σ u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 u) (fun _ ↦ (1 : ℝ)) ≤
      IEANTN.zetaN' σ v := by
  classical
  have hfin := finite_zero_rectangle (Set.Ioo σ 1) (T := u)
  have hfin' : (IEANTN.zetaZeroesIn (Set.Ioo σ 1) (Set.Ioo 0 v)).Finite :=
    (finite_zero_rectangle (Set.Ioo σ 1) (T := v)).subset
      (fun ρ hρ ↦ ⟨hρ.1, ⟨hρ.2.1.1, hρ.2.1.2.le⟩, hρ.2.2⟩)
  rw [IEANTN.zetaN', rectangle_sum_eq hfin, rectangle_sum_eq hfin']
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    exact ⟨hρ.1, ⟨hρ.2.1.1, hρ.2.1.2.trans_lt huv⟩, hρ.2.2⟩
  · intro ρ hρ _
    have hh := (Set.Finite.mem_toFinset hfin').mp hρ
    exact mul_nonneg (by norm_num) (CH2Section7Z.zetaOrder_nonneg_of_mem
      Set.Ioo_subset_Ioi_self ⟨trivial, hh.2.1, hh.2.2⟩)

/-- Pass the published strict FKS height convention to the closed cutoff by continuity. -/
theorem fks_density_closed (hFKS : FKS.v3.density_0618)
    {σ T : ℝ} (hσ : 3 / 4 ≤ σ) (hσ' : σ ≤ 7 / 8)
    (hT : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ T) :
    IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 T) (fun _ ↦ (1 : ℝ)) ≤
      fksDensityMajorant σ T := by
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 * 10 ^ 12) hT
  have hT1 : 1 < T := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3 * 10 ^ 12) hT
  have hlog : 0 < Real.log T := Real.log_pos hT1
  have hTne : T ≠ 0 := hT0.ne'
  have hlogne : Real.log T ≠ 0 := hlog.ne' 
  have hcont : ContinuousAt (fksDensityMajorant σ) T := by
    have hp := Real.continuousAt_rpow_const T (8 * (1 - σ) / 3) (Or.inl hTne)
    have hl := Real.continuousAt_log hTne
    have hq := (Real.continuousAt_rpow_const (Real.log T) (5 - 2 * σ)
      (Or.inl hlogne)).comp hl
    exact ((continuousAt_const.mul hp).mul hq).add (continuousAt_const.mul (hl.pow 2))
  have hlim : Tendsto (fksDensityMajorant σ) (𝓝[>] T) (𝓝 (fksDensityMajorant σ T)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (density_closed_le_open hT0.le hv).trans (hFKS σ v hσ hσ' (hT.trans hv.le))

/-- A cumulative finite density majorant controls the reciprocal-height tail. -/
theorem finite_reciprocal_majorant {α : Type*} (S : Finset α) (γ w : α → ℝ)
    {H T : ℝ} (hH : 0 < H) (hHT : H ≤ T)
    (hγ : ∀ z ∈ S, H < γ z ∧ γ z ≤ T) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Set.uIcc H T))
    (hcount : ∀ t ∈ Set.Icc H T, (∑ z ∈ S, if γ z ≤ t then w z else 0) ≤ F t) :
    (∑ z ∈ S, w z / γ z) ≤ F T / T + ∫ t in H..T, F t / t ^ 2 := by
  obtain ⟨hid, hi⟩ := finite_reciprocal_partial_sum S γ w hH hHT hγ
  have hT0 : 0 < T := hH.trans_le hHT
  have hFi : IntervalIntegrable (fun t ↦ F t / t ^ 2) volume H T := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htc := ht
    rw [Set.uIcc_of_le hHT] at htc
    have htpos : 0 < t := by linarith [htc.1]
    have ht0 : t ^ 2 ≠ 0 := by positivity
    exact (hF t ht).div (by fun_prop) ht0
  have hI := intervalIntegral.integral_mono_on hHT hi hFi (fun t ht ↦ ?_)
  swap
  · have ht0 : 0 < t := by linarith [ht.1]
    exact div_le_div_of_nonneg_right (hcount t ht) (by positivity)
  have hC : (∑ z ∈ S, w z) ≤ F T := by
    have hh := hcount T ⟨hHT, le_rfl⟩
    have he : (∑ z ∈ S, if γ z ≤ T then w z else 0) = ∑ z ∈ S, w z := by
      apply Finset.sum_congr rfl
      intro z hz
      exact if_pos (hγ z hz).2
    rwa [he] at hh
  rw [hid]
  exact add_le_add (div_le_div_of_nonneg_right hC hT0.le) hI

/-- The source FKS majorant is continuous at every admissible positive height. -/
theorem fksDensityMajorant_continuousAt {σ T : ℝ} (hT : 1 < T) :
    ContinuousAt (fksDensityMajorant σ) T := by
  have hTne : T ≠ 0 := by linarith
  have hl := Real.continuousAt_log hTne
  have hlogne : Real.log T ≠ 0 := (Real.log_pos hT).ne'
  have hp := Real.continuousAt_rpow_const T (8 * (1 - σ) / 3) (Or.inl hTne)
  have hq := (Real.continuousAt_rpow_const (Real.log T) (5 - 2 * σ)
    (Or.inl hlogne)).comp hl
  exact ((continuousAt_const.mul hp).mul hq).add (continuousAt_const.mul (hl.pow 2))

/-- Closed density counts inside a fixed larger finite rectangle. -/
theorem density_closed_eq_sum {σ t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 u) (fun _ ↦ (1 : ℝ)) =
      ∑ ρ ∈ (finite_zero_rectangle (Set.Ioo σ 1) (T := t)).toFinset,
        if ρ.im ≤ u then (IEANTN.zetaOrder ρ : ℝ) else 0 := by
  classical
  have hfu := finite_zero_rectangle (Set.Ioo σ 1) (T := u)
  have hft := finite_zero_rectangle (Set.Ioo σ 1) (T := t)
  rw [rectangle_sum_eq hfu]
  have he : hfu.toFinset = hft.toFinset.filter (fun ρ ↦ ρ.im ≤ u) := by
    ext ρ
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
    constructor
    · intro hρ
      exact ⟨⟨hρ.1, ⟨hρ.2.1.1, hρ.2.1.2.trans hut⟩, hρ.2.2⟩, hρ.2.1.2⟩
    · rintro ⟨hρ, hi⟩
      exact ⟨hρ.1, ⟨hρ.2.1.1, hi⟩, hρ.2.2⟩
  rw [he, Finset.sum_filter]
  simp only [one_mul]

/-- Use the actual FKS count and verified-height RH to bound the reciprocal zero tail. -/
theorem density_reciprocal_tail_le (hFKS : FKS.v3.density_0618)
    (hRH : IEANTN.RiemannHypothesisUpTo (3 * (10 : ℝ) ^ (12 : ℕ)))
    {σ t : ℝ} (hσ : 3 / 4 ≤ σ) (hσ' : σ ≤ 7 / 8)
    (ht : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ t) :
    IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t) (fun ρ ↦ 1 / ρ.im) ≤
      fksDensityMajorant σ t / t +
        ∫ u in (3 * (10 : ℝ) ^ (12 : ℕ))..t, fksDensityMajorant σ u / u ^ 2 := by
  classical
  set H : ℝ := 3 * (10 : ℝ) ^ (12 : ℕ) with hH
  have hH0 : 0 < H := by dsimp [H]; norm_num
  have hH1 : 1 < H := by dsimp [H]; norm_num
  have hfin := finite_zero_rectangle (Set.Ioo σ 1) (T := t)
  set S := hfin.toFinset with hS
  have hγ : ∀ ρ ∈ S, H < ρ.im ∧ ρ.im ≤ t := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset hfin).mp hρ
    refine ⟨?_, hh.2.1.2⟩
    by_contra he
    have hhH : ρ ∈ IEANTN.zetaZeroesIn (Set.Ioo (1 / 2) 1) (Set.Icc 0 H) :=
      ⟨⟨by linarith [hh.1.1], hh.1.2⟩, ⟨hh.2.1.1.le, not_lt.mp he⟩, hh.2.2⟩
    exact hRH.false ⟨ρ, hhH⟩
  have hcont : ContinuousOn (fksDensityMajorant σ) (Set.uIcc H t) := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    exact (fksDensityMajorant_continuousAt (hH1.trans_le hu.1)).continuousWithinAt
  have hc : ∀ u ∈ Set.Icc H t,
      (∑ ρ ∈ S, if ρ.im ≤ u then (IEANTN.zetaOrder ρ : ℝ) else 0) ≤ fksDensityMajorant σ u := by
    intro u hu
    rw [← density_closed_eq_sum (hH0.le.trans hu.1) hu.2]
    exact fks_density_closed hFKS hσ hσ' hu.1
  have hh := finite_reciprocal_majorant S Complex.im
    (fun ρ ↦ (IEANTN.zetaOrder ρ : ℝ)) hH0 ht hγ (fksDensityMajorant σ) hcont hc
  rw [rectangle_sum_eq hfin]
  simpa only [div_mul_eq_mul_div, one_mul] using hh

/-- A finite-height normalized density bound for the CH2 ordinate majorant. -/
noncomputable def finiteDensityWeight (σ t : ℝ) : ℝ :=
  2 * (fksDensityMajorant σ t / t +
    ∫ u in (3 * (10 : ℝ) ^ (12 : ℕ))..t, fksDensityMajorant σ u / u ^ 2) +
    4 * Real.pi / t * fksDensityMajorant σ t

/-- The actual FKS/RH inputs bound the normalized high-real-part spectral weight. -/
theorem density_ordinate_majorant_le (hFKS : FKS.v3.density_0618)
    (hRH : IEANTN.RiemannHypothesisUpTo (3 * (10 : ℝ) ^ (12 : ℕ)))
    {σ t : ℝ} (hσ : 3 / 4 ≤ σ) (hσ' : σ ≤ 7 / 8)
    (ht : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ t) :
    (2 * Real.pi / t) * IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t)
      (fun ρ ↦ t / Real.pi * (1 / ρ.im) + 2) ≤ finiteDensityWeight σ t := by
  classical
  have hp := Real.pi_pos
  have ht0 : 0 < t := by norm_num at ht; linarith
  have hfin := finite_zero_rectangle (Set.Ioo σ 1) (T := t)
  have he : IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t)
      (fun ρ ↦ t / Real.pi * (1 / ρ.im) + 2) =
      t / Real.pi * IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t) (fun ρ ↦ 1 / ρ.im) +
      2 * IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t) (fun _ ↦ 1) := by
    rw [rectangle_sum_eq hfin, rectangle_sum_eq hfin, rectangle_sum_eq hfin,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  have hI := mul_le_mul_of_nonneg_left (density_reciprocal_tail_le hFKS hRH hσ hσ' ht)
    (show 0 ≤ t / Real.pi by positivity)
  have hN := mul_le_mul_of_nonneg_left (fks_density_closed hFKS hσ hσ' ht)
    (by norm_num : (0 : ℝ) ≤ 2)
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (add_le_add hI hN)
    (show 0 ≤ 2 * Real.pi / t by positivity)
  refine hh.trans_eq ?_
  unfold finiteDensityWeight
  field_simp
  ring

end CH2QRH
