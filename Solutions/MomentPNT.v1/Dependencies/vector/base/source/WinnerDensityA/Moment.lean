/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityHeight
import Mathlib.Tactic
open Complex Filter Topology Set MeasureTheory
namespace WinnerDensityA
open CH2QRH
abbrev H : ℝ := 3000000000000
noncomputable def poly (c d σ t : ℝ) :=
  c * t ^ (8*(1-σ)/3) * Real.log t ^ (5-2*σ) + d * Real.log t ^ (2:ℕ)
/-- A published density input, before any new reciprocal/grid/PNT reduction. -/
def DensityInput (c d : ℝ → ℝ) : Prop :=
  ∀ σ t : ℝ, (3/4:ℝ) ≤ σ → σ ≤ 7/8 → H ≤ t →
    IEANTN.zetaN' σ t ≤ poly (c σ) (d σ) σ t
noncomputable def moment (c d σ : ℝ) :=
  c * densityMomentMain σ H + d * ((Real.log H ^ (2:ℕ)+2*Real.log H+2)/H)
noncomputable def envelope (c d σ τ : ℝ) :=
  2*moment c d σ + 4*Real.pi*(poly c d σ (Real.exp τ)/Real.exp τ)

theorem poly_continuous {c d σ t : ℝ} (ht : 1 < t) : ContinuousAt (poly c d σ) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl := Real.continuousAt_log ht0
  have hln : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  unfold poly
  exact ((continuousAt_const.mul (Real.continuousAt_rpow_const t _ (Or.inl ht0))).mul
    (hl.rpow_const (Or.inl hln))).add (continuousAt_const.mul (hl.pow 2))

theorem count_closed {c d σ T : ℝ} (hT : H ≤ T)
    (hc : ∀ u : ℝ, H ≤ u → IEANTN.zetaN' σ u ≤ poly c d σ u) :
    IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 T) (fun _ ↦ (1:ℝ)) ≤ poly c d σ T := by
  have ht0 : 0 < T := by norm_num [H] at hT; linarith
  have ht1 : 1 < T := by norm_num [H] at hT; linarith
  have hlim : Tendsto (poly c d σ) (𝓝[>] T) (𝓝 (poly c d σ T)) :=
    (poly_continuous (c:=c) (d:=d) (σ:=σ) ht1).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (density_closed_le_open ht0.le hu).trans (hc u (hT.trans hu.le))

theorem reciprocal_tail {c d σ t : ℝ} (hσ : (3/4:ℝ) ≤ σ) (ht : H ≤ t)
    (hRH : IEANTN.RiemannHypothesisUpTo H)
    (hcount : ∀ u : ℝ, H ≤ u → IEANTN.zetaN' σ u ≤ poly c d σ u) :
    IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t) (fun ρ ↦ 1/ρ.im) ≤
      poly c d σ t/t + ∫ u in H..t, poly c d σ u/u^2 := by
  classical
  have hH0 : 0 < H := by norm_num [H]
  have hH1 : 1 < H := by norm_num [H]
  have hfin := finite_zero_rectangle (Set.Ioo σ 1) (T:=t)
  let S := hfin.toFinset
  have hγ : ∀ ρ ∈ S, H < ρ.im ∧ ρ.im ≤ t := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset hfin).mp hρ
    refine ⟨?_,hh.2.1.2⟩
    by_contra he
    have hi : ρ ∈ IEANTN.zetaZeroesIn (Set.Ioo (1/2) 1) (Set.Icc 0 H) :=
      ⟨⟨by linarith [hh.1.1],hh.1.2⟩,⟨hh.2.1.1.le,not_lt.mp he⟩,hh.2.2⟩
    exact hRH.false ⟨ρ,hi⟩
  have hcont : ContinuousOn (poly c d σ) (Set.uIcc H t) := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    exact (poly_continuous (hH1.trans_le hu.1)).continuousWithinAt
  have hc : ∀ u ∈ Set.Icc H t,
      (∑ ρ ∈ S, if ρ.im ≤ u then (IEANTN.zetaOrder ρ:ℝ) else 0) ≤ poly c d σ u := by
    intro u hu
    rw [← density_closed_eq_sum (hH0.le.trans hu.1) hu.2]
    exact count_closed hu.1 hcount
  have hh := finite_reciprocal_majorant S Complex.im (fun ρ ↦ (IEANTN.zetaOrder ρ:ℝ))
    hH0 ht hγ (poly c d σ) hcont hc
  rw [rectangle_sum_eq hfin]
  simpa only [div_mul_eq_mul_div,one_mul] using hh

theorem moment_bound {c d σ T : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hσ : (3/4:ℝ) ≤ σ) (hσ' : σ ≤ 7/8) (hT : H ≤ T) :
    poly c d σ T/T + (∫ u in H..T, poly c d σ u/u^2) ≤ moment c d σ := by
  have hH : 1 < H := by norm_num [H]
  have h1 := power_log_tail_four (p:=8*(1-σ)/3) (q:=5-2*σ) hH hT
    (by linarith) (by linarith) (by linarith) (by linarith)
  have h2 := log_square_reciprocal_tail hH hT
  have hi1 := power_log_intervalIntegrable (p:=8*(1-σ)/3) (q:=5-2*σ) hH hT
  have hi2 := power_log_intervalIntegrable (p:=0) (q:=2) hH hT
  have he : (fun u : ℝ ↦ poly c d σ u/u^2) =
      (fun u ↦ c*(u^(8*(1-σ)/3)*Real.log u^(5-2*σ)/u^2)+
        d*(u^(0:ℝ)*Real.log u^(2:ℝ)/u^2)) := by
    funext u; simp only [poly,Real.rpow_zero,Real.rpow_two]; ring
  rw [he,intervalIntegral.integral_add (hi1.const_mul c) (hi2.const_mul d),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  simp only [poly,Real.rpow_zero,Real.rpow_two,one_mul] at *
  have hh1 := mul_le_mul_of_nonneg_left h1 hc
  have hh2 := mul_le_mul_of_nonneg_left h2 hd
  convert add_le_add hh1 hh2 using 1 <;> first | rfl | ring

theorem boundary_antitone {c d σ U : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hσ : (3/4:ℝ) ≤ σ) (hσ' : σ ≤ 7/8) (hU : 1 < U) (hl : 28 ≤ Real.log U) :
    AntitoneOn (fun t ↦ poly c d σ t/t) (Set.Ici U) := by
  have hl0 : 0 < Real.log U := by linarith
  have hq : 0 ≤ 5-2*σ := by linarith
  have hr : (5-2*σ)/Real.log U ≤ 1/8 := by
    apply (div_le_iff₀ hl0).mpr; linarith
  have hr2 : (2:ℝ)/Real.log U ≤ 1/14 := by
    apply (div_le_iff₀ hl0).mpr; linarith
  have h1 := power_log_boundary_antitone (p:=8*(1-σ)/3) hU hq (by linarith)
  have h2 := power_log_boundary_antitone (p:=0) (q:=2) hU (by norm_num) (by linarith)
  intro u hu v hv huv
  have hu0 : 0 < u := by have : U ≤ u := hu; linarith
  have hv0 : 0 < v := by have : U ≤ v := hv; linarith
  have hh1 := h1 hu hv huv
  have hh2 := h2 hu hv huv
  have he : ∀ t : ℝ, 0 < t → poly c d σ t/t =
      c*(t^(8*(1-σ)/3-1)*Real.log t^(5-2*σ)) + d*(t^(-1:ℝ)*Real.log t^(2:ℕ)) := by
    intro t ht; simp only [poly,Real.rpow_sub ht,Real.rpow_one,Real.rpow_neg_one]; ring
  change poly c d σ v/v ≤ poly c d σ u/u
  rw [he u hu0,he v hv0]
  norm_num [Real.rpow_two] at hh2
  nlinarith [mul_le_mul_of_nonneg_left hh1 hc,mul_le_mul_of_nonneg_left hh2 hd]

/-- A fixed envelope controls actual finite spectral weights at every larger height. -/
theorem ordinate_envelope {c d σ τ t : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hσ : (3/4:ℝ) ≤ σ) (hσ' : σ ≤ 7/8) (hτ : 28 ≤ τ)
    (hτH : H ≤ Real.exp τ) (ht : Real.exp τ ≤ t)
    (hRH : IEANTN.RiemannHypothesisUpTo H)
    (hcount : ∀ u : ℝ, H ≤ u → IEANTN.zetaN' σ u ≤ poly c d σ u) :
    (2*Real.pi/t)*IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t)
      (fun ρ ↦ t/Real.pi*(1/ρ.im)+2) ≤ envelope c d σ τ := by
  have htH := hτH.trans ht
  have ht0 : 0 < t := by norm_num [H] at htH; linarith
  have hfin := finite_zero_rectangle (Set.Ioo σ 1) (T:=t)
  have he : IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t)
      (fun ρ ↦ t/Real.pi*(1/ρ.im)+2) =
      t/Real.pi*IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t) (fun ρ ↦ 1/ρ.im)+
      2*IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t) (fun _ ↦ (1:ℝ)) := by
    rw [rectangle_sum_eq hfin,rectangle_sum_eq hfin,rectangle_sum_eq hfin,
      Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro ρ _; ring
  have hR := (reciprocal_tail hσ htH hRH hcount).trans (moment_bound hc hd hσ hσ' htH)
  have hN := count_closed htH hcount
  have hB := boundary_antitone hc hd hσ hσ'
    (show 1 < Real.exp τ by rw [Real.one_lt_exp_iff]; linarith) (by simpa using hτ)
  have hBd := hB (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  rw [he]
  have hh1 := mul_le_mul_of_nonneg_left hR (show 0 ≤ t/Real.pi by positivity)
  have hh2 := mul_le_mul_of_nonneg_left hN (show (0:ℝ) ≤ 2 by norm_num)
  have hh := mul_le_mul_of_nonneg_left (add_le_add hh1 hh2) (show 0 ≤ 2*Real.pi/t by positivity)
  have hp := mul_le_mul_of_nonneg_left hBd (show 0 ≤ 4*Real.pi by positivity)
  unfold envelope
  have hid : (2*Real.pi/t)*(t/Real.pi*moment c d σ+2*poly c d σ t) =
      2*moment c d σ+4*Real.pi*(poly c d σ t/t) := by field_simp; ring
  rw [hid] at hh
  linarith
end WinnerDensityA
#print axioms WinnerDensityA.ordinate_envelope
