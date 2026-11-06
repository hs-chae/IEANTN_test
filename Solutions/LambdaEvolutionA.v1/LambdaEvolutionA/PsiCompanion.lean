/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LambdaEvolutionA.DirectLambda
import LambdaEvolutionA.EnvelopeTransfer
/-! Matched genuineψ companion and elementary9κ weighted baseline.
The source package and numerical coefficient are exactly those of the direct
weighted consumer. Noπ theorem is reinterpreted asψ. -/
namespace LambdaEvolutionA
open Complex Filter Topology Set MeasureTheory Real WinnerDensityA
open CH2QRH CH2.v7 CH2Section6 CH2Section81 CH2Section9
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Actualψ envelope from the old CH2 raw transfer and the same density profile. -/
theorem psi_companion_row_normalized (hs : DirectCH2Inputs)
    (accepted : ∀j:Fin 18,WinnerProgramA.acceptUpper
      (PVEvolutionA.Recovery.GaussianBasis.output j)
      [(PVEvolutionA.Recovery.GaussianBasis.spec j).cap]=true)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {n:ℕ} (hn:0<n) {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    IEANTN.Eψ x*x^((1:ℝ)/8)≤
      PVEvolutionA.Recovery.Numerical.coefficient n 330 100 := by
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  let L := Real.log x
  let k : ℝ := 1/3
  let T : ℝ := Real.exp (k*L)+1/2
  have hL : (330:ℝ)≤L := by
    have hh := Real.log_le_log (Real.exp_pos 330) hx
    simpa only [Real.log_exp] using hh
  have hL64 : 64≤Real.log x := by dsimp [L] at hL;linarith
  have hk : k≤7/10 := by norm_num [k]
  have hsep : 34≤k*Real.log x-Real.log x/8 := by dsimp [k];dsimp [L] at hL;linarith
  obtain ⟨hTlo,hR,hxlo,_,_,hlogT⟩ := density_height_parameters hx0 hL64 hk hsep
  have hTlo' : H+1≤T := by norm_num [H] at hTlo ⊢;exact hTlo
  obtain ⟨t,ht,hE⟩ := WinnerDensityA.raw_finite_transfer hs.hfe hs.hdig hs.h24u hs.h24l
    hs.hk hs.hneg hs.h2v hs.hv hs.hcs hs.hrvm hs.hsmall hs.hlow hs.hH hTlo' hR hxlo (by linarith)
  have h100 : H≤Real.exp (100:ℝ) := by
    have hh := (CH2Section7A.exp_nat_bounds 44).1
    have he := Real.exp_le_exp.mpr (show (44:ℝ)≤100 by norm_num)
    norm_num [H] at hh ⊢
    linarith
  have htexp : Real.exp (100:ℝ)≤t := by
    have he : Real.exp (100:ℝ)≤Real.exp (k*L) := Real.exp_le_exp.mpr (by dsimp [k];linarith)
    exact he.trans (show Real.exp (k*L)≤t by simpa only [T,add_sub_cancel_right] using ht.1)
  have ht1 : 1≤t := (Real.one_le_exp (by norm_num : (0:ℝ)≤100)).trans htexp
  have htlog : Real.log t≤((110:ℝ)/330)*L+(1:ℝ)/10^9 := by
    have htT : t≤T := ht.2
    have hb := (Real.log_le_log (by linarith : 0<t) htT).trans hlogT
    norm_num only [show (110:ℝ)/330=1/3 by norm_num]
    convert! hb using 1 <;> norm_num [k,L]
  have hbase := density_count_base_row (by norm_num : (64:ℝ)≤330) hL
    (by norm_num : (44:ℝ)≤110) ht1 htlog
  have hrem := density_remainder_coefficient hx0 hL64 hk hsep
  have ha := PVEvolutionA.graded_monotone n
  have ha0 := PVEvolutionA.graded_zero hn
  have han := PVEvolutionA.graded_last n
  have hQ : ∀i≤n,(2*Real.pi/t)*IEANTN.zetaZeroesSum
      (Ioo (PVEvolutionA.gradedGrid n i) 1) (Ioc 0 t)
      (fun rho↦t/Real.pi*(1/rho.im)+2)≤
        PVEvolutionA.Recovery.Model.envelope (PVEvolutionA.gradedGrid n i) 100 := by
    intro i hi
    have hlo : (3/4:ℝ)≤PVEvolutionA.gradedGrid n i := by rw [←ha0];exact ha (Nat.zero_le i)
    have hhi : PVEvolutionA.gradedGrid n i≤(7/8:ℝ) := by rw [←han];exact ha hi
    exact PVEvolutionA.Recovery.Model.source_ordinate_envelope accepted h hRH hlo hhi
      (by norm_num) h100 htexp
  have hspec := spectral_grid_abstract hs.hrvm hs.hsmall hs.hlow
    (by have hh:=h100.trans htexp;norm_num [H] at hh;linarith : 1000≤t)
    hx0 (by norm_num : (0:ℝ)≤330) hL hqrh
    (PVEvolutionA.gradedGrid n) ha n ha0 han
    (fun s↦PVEvolutionA.Recovery.Model.envelope s 100) hQ
  have hscaled := mul_le_mul_of_nonneg_right hE (Real.rpow_pos_of_pos hx0 ((1:ℝ)/8)).le
  rw [add_mul] at hscaled
  unfold PVEvolutionA.Recovery.Numerical.coefficient
  dsimp only [L,T,k] at *
  norm_num only [show (330:ℝ)/3=110 by norm_num]
  linarith only [hscaled,hspec,hbase,hrem]

/-- The same exact executed coefficient now bounds the actualψ error. -/
theorem psi_companion330 (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    IEANTN.Eψ x≤
      (1826923053/200000000000:ℝ)*x^(-(1:ℝ)/8) := by
  have hp := psi_companion_row_normalized hs PVEvolutionA.Recovery.GaussianBasis.accepted
    h hRH hqrh (n:=PVEvolutionA.Recovery.Ray.sigmaCells)
    (by norm_num [PVEvolutionA.Recovery.Ray.sigmaCells]) hx
  have hc := PVEvolutionA.Recovery.Mixed.coefficient_of_checks
    PVEvolutionA.Recovery.Mixed.base_checked PVEvolutionA.Recovery.Mixed.checked_all
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  have hb := hp.trans hc
  rw [show -(1:ℝ)/8=-((1:ℝ)/8) by ring,Real.rpow_neg hx0.le]
  exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hx0 _)).mpr hb

/-- Friendlyψ coefficient appearing in the separate allowance comparison. -/
theorem psi_companion330_friendly (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    IEANTN.Eψ x≤(9134616/1000000000:ℝ)*x^(-(1:ℝ)/8) := by
  exact (psi_companion330 hs h hRH hqrh hx).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg ((Real.exp_pos 330).trans_le hx).le _))

/-- The genuine elementary9κ baseline, with exactly the same source package. -/
theorem matched_flat_lambda330 (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤
      (9*(1826923053/200000000000:ℝ))*x^(-(1:ℝ)/8) := by
  exact lambda_error_le_power
    (Real.one_le_exp (by norm_num : (0:ℝ)≤330))
    (fun t ht↦psi_companion330 hs h hRH hqrh ht) hx

/-- Strict comparison of proved allowance functions on everypositive realx. -/
theorem matched_allowance_strict {x:ℝ} (hx:0<x) :
    (1826923053/200000000000:ℝ)*x^(-(1:ℝ)/8)<
      (9*(1826923053/200000000000:ℝ))*x^(-(1:ℝ)/8) := by
  exact mul_lt_mul_of_pos_right (by norm_num) (Real.rpow_pos_of_pos hx _)

/-- Both valid weighted bounds and their strict stated-allowance comparison. -/
theorem matched_direct_and_flat330 (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    (|CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤
      (1826923053/200000000000:ℝ)*x^(-(1:ℝ)/8)) ∧
    (|CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤
      (9*(1826923053/200000000000:ℝ))*x^(-(1:ℝ)/8)) ∧
    ((1826923053/200000000000:ℝ)*x^(-(1:ℝ)/8)<
      (9*(1826923053/200000000000:ℝ))*x^(-(1:ℝ)/8)) := by
  exact ⟨direct_lambda330 hs h hRH hqrh hx,
    matched_flat_lambda330 hs h hRH hqrh hx,
    matched_allowance_strict ((Real.exp_pos 330).trans_le hx)⟩

#print axioms psi_companion330
#print axioms psi_companion330_friendly
#print axioms matched_flat_lambda330
#print axioms matched_allowance_strict
#print axioms matched_direct_and_flat330
end LambdaEvolutionA
