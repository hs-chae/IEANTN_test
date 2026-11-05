/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.Spectral
import DensityRay
open Complex Filter Topology Set MeasureTheory
namespace WinnerDensityA
open CH2QRH CH2.v7
noncomputable def rowCoefficient (c d : ℝ → ℝ) (a : ℕ → ℝ) (n : ℕ) (L τ : ℝ) :=
  gridCoefficient (fun σ ↦ envelope (c σ) (d σ) σ τ) a n L+
    Real.exp (-L/8)*((τ+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*(τ+(1:ℝ)/10^9))+1/10^12

/-- An actual whole-ray prime-error theorem consuming a finite discrete density coefficient.
The only density premise is the named upstream zero-count statement, not a new moment or PNT oracle. -/
theorem psi_row_normalized
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper) (h24l : CH2.v2.proposition_2_4_lower)
    (hk_ : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (c d : ℝ → ℝ) (hDensity : DensityInput c d)
    (hcoeff : ∀ σ ∈ Set.Icc (3/4:ℝ) (7/8),0≤c σ ∧ 0≤d σ)
    (hRH : IEANTN.RiemannHypothesisUpTo H)
    (a : ℕ → ℝ) (ha : Monotone a) (n : ℕ) (ha0 : a 0=3/4) (han : a n=7/8)
    {L0 τ x : ℝ} (hL0 : 64≤L0) (hτ : 44≤τ) (hk0 : τ≤(7/10)*L0)
    (hsep0 : 34≤τ-L0/8) (hx : Real.exp L0≤x)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8)) :
    IEANTN.Eψ x*x^((1:ℝ)/8) ≤ rowCoefficient c d a n L0 τ := by
  have hx0 : 0<x := (Real.exp_pos L0).trans_le hx
  let L := Real.log x
  let k := τ/L0
  let T := Real.exp (k*L)+1/2
  have hL00 : 0<L0 := by linarith
  have hL : L0≤L := by
    have hh := Real.log_le_log (Real.exp_pos L0) hx
    simpa [L] using hh
  have hL64 : 64≤Real.log x := hL0.trans hL
  have hk : k≤7/10 := (div_le_iff₀ hL00).mpr hk0
  have hkL0 : k*L0=τ := by dsimp [k];field_simp
  have hkpos : 0<k := by dsimp [k];positivity
  have hslope : 0≤k-1/8 := by nlinarith
  have hsep : 34≤k*Real.log x-Real.log x/8 := by
    have hh := mul_le_mul_of_nonneg_left hL hslope
    dsimp [L] at hh;nlinarith
  obtain ⟨hTlo,hR,hxlo,_,_,hlogT⟩ := density_height_parameters hx0 hL64 hk hsep
  have hTlo' : H+1≤T := by norm_num [H] at hTlo ⊢;exact hTlo
  obtain ⟨t,ht,hE⟩ := raw_finite_transfer hfe hdig h24u h24l hk_ hneg h2v hv hcs
    hrvm hsmall hlow hH hTlo' hR hxlo (by linarith)
  have htexp : Real.exp τ≤t := by
    have hh := mul_le_mul_of_nonneg_left hL hkpos.le
    rw [hkL0] at hh
    have he := Real.exp_le_exp.mpr hh
    have hlo : Real.exp (k*L)≤t := by simpa [T] using ht.1
    exact he.trans hlo
  have hτH : H≤Real.exp τ := by
    have hh := (CH2Section7A.exp_nat_bounds 44).1
    have he := Real.exp_le_exp.mpr hτ
    norm_num [H] at hh ⊢;linarith
  have ht1 : 1≤t := (show 1≤Real.exp τ by rw [Real.one_le_exp_iff];linarith).trans htexp
  have htlog : Real.log t≤τ/L0*L+(1:ℝ)/10^9 := by
    have htT : t≤T := ht.2
    exact (Real.log_le_log (by linarith : 0<t) htT).trans hlogT
  have hbase := density_count_base_row hL0 hL hτ ht1 htlog
  have hrem := density_remainder_coefficient hx0 hL64 hk hsep
  have hQ : ∀ i≤n,(2*Real.pi/t)*IEANTN.zetaZeroesSum (Set.Ioo (a i) 1) (Set.Ioc 0 t)
      (fun ρ ↦ t/Real.pi*(1/ρ.im)+2) ≤ envelope (c (a i)) (d (a i)) (a i) τ := by
    intro i hi
    have hlo : (3/4:ℝ)≤a i := by rw [←ha0];exact ha (Nat.zero_le i)
    have hhi : a i≤(7/8:ℝ) := by rw [←han];exact ha hi
    exact ordinate_envelope (hcoeff _ ⟨hlo,hhi⟩).1 (hcoeff _ ⟨hlo,hhi⟩).2 hlo hhi
      (by linarith) hτH htexp hRH (fun u hu ↦ hDensity _ _ hlo hhi hu)
  have hspec := spectral_grid_abstract hrvm hsmall hlow
    (by have hh:=hτH.trans htexp;norm_num [H] at hh;linarith : 1000≤t)
    hx0 (by linarith : 0≤L0) hL hqrh a ha n ha0 han (fun σ ↦ envelope (c σ) (d σ) σ τ) hQ
  have hscaled := mul_le_mul_of_nonneg_right hE (Real.rpow_pos_of_pos hx0 ((1:ℝ)/8)).le
  rw [add_mul] at hscaled
  unfold rowCoefficient
  dsimp [L,T] at *
  linarith only [hscaled,hspec,hbase,hrem]

/-- A certified coefficient becomes a genuine pointwise bound, uniformly on its ray. -/
theorem psi_of_normalized {C x : ℝ} (hx : 0<x)
    (h : IEANTN.Eψ x*x^((1:ℝ)/8)≤C) :
    IEANTN.Eψ x≤C*x^(-(1:ℝ)/8) := by
  rw [show -(1:ℝ)/8=-((1:ℝ)/8) by ring,Real.rpow_neg hx.le]
  exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hx _)).mpr h
end WinnerDensityA
#print axioms WinnerDensityA.psi_row_normalized
