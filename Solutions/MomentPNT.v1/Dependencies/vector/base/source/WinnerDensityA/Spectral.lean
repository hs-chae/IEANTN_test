/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.Raw
import WinnerDensityA.Grid
open Complex Filter Topology Set MeasureTheory
namespace WinnerDensityA
open CH2QRH CH2.v7
noncomputable def gridCoefficient (Q : ℝ → ℝ) (a : ℕ → ℝ) (n : ℕ) (L : ℝ) :=
  Real.exp (L*(a 0-7/8))*Q (a 0)+
    ∑ i ∈ Finset.range n, (Real.exp (L*(a (i+1)-7/8))-Real.exp (L*(a i-7/8)))*Q (a i)

/-- The new discrete reduction bounds the actual spectral sum at every larger x.
The high-zero powers decrease individually; no false monotonicity of L times an integral is used. -/
theorem spectral_grid_abstract
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {t x L0 : ℝ} (ht : 1000 ≤ t) (hx : 0 < x) (hL0 : 0 ≤ L0)
    (hL : L0 ≤ Real.log x) (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    (a : ℕ → ℝ) (ha : Monotone a) (n : ℕ) (ha0 : a 0=3/4) (han : a n=7/8)
    (Q : ℝ → ℝ)
    (hQ : ∀ i≤n, (2*Real.pi/t)*IEANTN.zetaZeroesSum (Set.Ioo (a i) 1) (Set.Ioc 0 t)
      (fun ρ ↦ t/Real.pi*(1/ρ.im)+2) ≤ Q (a i)) :
    rawSpectral t x*x^((1:ℝ)/8) ≤
      Real.exp (-Real.log x/8)*spectralBound t+gridCoefficient Q a n L0 := by
  classical
  have ht0 : 0<t := by linarith
  have hp := Real.pi_pos
  have hlog : 0≤Real.log x := hL0.trans hL
  have hfin := CH2Section7Z.finite_zeros_Ioc (a:=0) (b:=t) le_rfl
  let S := hfin.toFinset
  let w : ℂ → ℝ := fun ρ ↦ (2*Real.pi/t)*(t/Real.pi*(1/ρ.im)+2)*(IEANTN.zetaOrder ρ:ℝ)
  let B : ℂ → ℝ := fun ρ ↦ Real.exp (Real.log x*(ρ.re-7/8))
  let SH := S.filter (fun ρ ↦ a 0<ρ.re)
  have hw : ∀ ρ ∈ S,0≤w ρ := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset hfin).mp hρ
    have hi := hh.2.1.1
    have hm := CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hh
    dsimp [w]; positivity
  have hb : ∀ ρ ∈ S,ρ.re≤(7/8:ℝ) := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset hfin).mp hρ
    exact re_le_boundary hqrh hh.2.2 hh.2.1.1
  have hcumulative : ∀ σ : ℝ, (∑ ρ ∈ S,if σ<ρ.re then w ρ else 0) =
      (2*Real.pi/t)*IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t)
        (fun ρ ↦ t/Real.pi*(1/ρ.im)+2) := by
    intro σ
    rw [←density_majorant_filter_eq,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro ρ _
    dsimp [w]
    split_ifs <;> ring
  have hhigh : ∀ σ : ℝ,a 0≤σ →
      (∑ ρ ∈ SH,if σ<ρ.re then w ρ else 0)=∑ ρ ∈ S,if σ<ρ.re then w ρ else 0 := by
    intro σ hσ
    rw [show SH=S.filter (fun ρ ↦ a 0<ρ.re) from rfl,Finset.sum_filter]
    apply Finset.sum_congr rfl;intro ρ _
    by_cases hi : σ<ρ.re
    · simp only [if_pos hi,if_pos (lt_of_le_of_lt hσ hi)]
    · simp only [if_neg hi,ite_self]
  have hbase : (∑ ρ ∈ SH,w ρ) ≤ Q (a 0) := by
    have he : (∑ ρ ∈ SH,w ρ) =∑ ρ ∈ S,if a 0<ρ.re then w ρ else 0 := by
      exact Finset.sum_filter ..
    rw [he,hcumulative]
    exact hQ 0 (Nat.zero_le n)
  let f : ℝ → ℝ := fun b ↦ Real.exp (L0*(b-7/8))
  have hf : Monotone f := by
    intro u v huv
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right huv _) hL0)
  have hgrid := weighted_step_majorant SH w Complex.re hf ha n
    (fun ρ hρ ↦ hw ρ (Finset.mem_filter.mp hρ).1)
    (fun ρ hρ ↦ by rw [han];exact hb ρ (Finset.mem_filter.mp hρ).1)
    Q (Real.exp_pos _).le hbase (fun i hi ↦ by
      rw [hhigh (a i) (ha (Nat.zero_le i)),hcumulative]
      exact hQ i hi.le)
  have hhi : (∑ ρ ∈ SH,w ρ*B ρ) ≤ gridCoefficient Q a n L0 := by
    apply (Finset.sum_le_sum (fun ρ hρ ↦ ?_)).trans hgrid
    apply mul_le_mul_of_nonneg_left _ (hw ρ (Finset.mem_filter.mp hρ).1)
    apply Real.exp_le_exp.mpr
    have hr := hb ρ (Finset.mem_filter.mp hρ).1
    change Real.log x*(ρ.re-7/8) ≤ L0*(ρ.re-7/8)
    nlinarith
  have hlo : (∑ ρ ∈ S,if ρ.re≤a 0 then w ρ*B ρ else 0) ≤
      Real.exp (Real.log x*(a 0-7/8))*(∑ ρ ∈ S,w ρ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ hρ
    by_cases hr : ρ.re≤a 0
    · rw [if_pos hr]
      have he : B ρ≤Real.exp (Real.log x*(a 0-7/8)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hr _) hlog
      nlinarith [mul_le_mul_of_nonneg_left he (hw ρ hρ)]
    · rw [if_neg hr]
      exact mul_nonneg (Real.exp_pos _).le (hw ρ hρ)
  have hwtotal : (∑ ρ ∈ S,w ρ)≤spectralBound t := by
    have hh := mul_le_mul_of_nonneg_left (ordinate_majorant_sum_le hrvm hsmall hlow ht)
      (show 0≤2*Real.pi/t by positivity)
    have he : (∑ ρ ∈ S,w ρ)=(2*Real.pi/t)*IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
        (fun ρ ↦ t/Real.pi*(1/ρ.im)+2) := by
      rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin,Finset.mul_sum]
      apply Finset.sum_congr rfl;intro ρ _
      dsimp [w];ring
    rw [he]
    exact hh.trans_eq (by field_simp)
  have hlo' := hlo.trans (mul_le_mul_of_nonneg_left hwtotal (Real.exp_pos _).le)
  rw [ha0,show Real.log x*((3/4:ℝ)-7/8)=-Real.log x/8 by ring] at hlo'
  have hsplit : (∑ ρ ∈ S,w ρ*B ρ)=
      (∑ ρ ∈ S,if ρ.re≤a 0 then w ρ*B ρ else 0)+(∑ ρ ∈ SH,w ρ*B ρ) := by
    rw [show SH=S.filter (fun ρ ↦ a 0<ρ.re) from rfl,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro ρ _
    by_cases hr : ρ.re≤a 0
    · rw [if_pos hr,if_neg (not_lt.mpr hr),add_zero]
    · rw [if_neg hr,if_pos (lt_of_not_ge hr),zero_add]
  have hraw : rawSpectral t x*x^((1:ℝ)/8)=∑ ρ ∈ S,w ρ*B ρ := by
    unfold rawSpectral
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl;intro ρ _
    dsimp [w,B]
    rw [show ((2*Real.pi/t)*((t/Real.pi*(1/ρ.im)+2)*x^(ρ.re-1)*(IEANTN.zetaOrder ρ:ℝ)))*
        x^((1:ℝ)/8)=(2*Real.pi/t)*(t/Real.pi*(1/ρ.im)+2)*(IEANTN.zetaOrder ρ:ℝ)*
        (x^(ρ.re-1)*x^((1:ℝ)/8)) by ring,
      ←Real.rpow_add hx,Real.rpow_def_of_pos hx]
    congr 1;congr 1;ring
  rw [hraw,hsplit]
  rw [ha0]
  exact add_le_add hlo' hhi
end WinnerDensityA
#print axioms WinnerDensityA.spectral_grid_abstract
