/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.FiniteTransfer
import PVEvolutionA.SlopedRayMid
/-! N analytic transport: numerical instances are inherited unchanged at00128.
No fresh program execution, array, profile or certificate is introduced. -/
namespace E1FrozenN
open Real Set MeasureTheory WinnerDensityA CH2QRH
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem coefficient_of_finite (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {n:ℕ} (hn:0<n) {x value:ℝ} (hx:Real.exp (330:ℝ)≤x)
    (hfinite : ∃t∈Icc (Real.exp ((1/3:ℝ)*Real.log x)-0)
      (Real.exp ((1/3:ℝ)*Real.log x)+1/2),
      value≤finiteRemainder (Real.exp ((1/3:ℝ)*Real.log x)+1/2) x+rawSpectral t x) :
    value*x^((1:ℝ)/8)≤
      PVEvolutionA.Separated.coefficient n 330 100 := by
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
  obtain ⟨t,ht,hE⟩ := hfinite
  have h100 : H≤Real.exp (100:ℝ) := by
    have hh := (CH2Section7A.exp_nat_bounds 44).1
    have he := Real.exp_le_exp.mpr (show (44:ℝ)≤100 by norm_num)
    norm_num [H] at hh ⊢
    linarith
  have htexp : Real.exp (100:ℝ)≤t := by
    have he : Real.exp (100:ℝ)≤Real.exp (k*L) := Real.exp_le_exp.mpr (by dsimp [k];linarith)
    exact he.trans (show Real.exp (k*L)≤t by simpa only [T,sub_zero] using ht.1)
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
        PVEvolutionA.SlopedProgram.mathEnvelope (PVEvolutionA.gradedGrid n i) 100 := by
    intro i hi
    have hlo : (3/4:ℝ)≤PVEvolutionA.gradedGrid n i := by rw [←ha0];exact ha (Nat.zero_le i)
    have hhi : PVEvolutionA.gradedGrid n i≤(7/8:ℝ) := by rw [←han];exact ha hi
    rw [PVEvolutionA.SlopedProgram.envelope_link]
    exact PVEvolutionA.SlopedMoment.source_ordinate_envelope h hRH hlo hhi
      (by norm_num) h100 htexp
  have hspec := spectral_grid_abstract hs.hrvm hs.hsmall hs.hlow
    (by have hh:=h100.trans htexp;norm_num [H] at hh;linarith : 1000≤t)
    hx0 (by norm_num : (0:ℝ)≤330) hL hqrh
    (PVEvolutionA.gradedGrid n) ha n ha0 han
    (fun s↦PVEvolutionA.SlopedProgram.mathEnvelope s 100) hQ
  have hscaled := mul_le_mul_of_nonneg_right hE (Real.rpow_pos_of_pos hx0 ((1:ℝ)/8)).le
  rw [add_mul] at hscaled
  unfold PVEvolutionA.Separated.coefficient
  dsimp only [L,T,k] at *
  norm_num only [show (330:ℝ)/3=110 by norm_num]
  linarith only [hscaled,hspec,hbase,hrem]


/-- Actual consumer using the old unchanged numerical cap. -/
theorem lambda330 (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤(9150520022/1000000000000:ℝ)*x^(-(1:ℝ)/8) := by
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  have hL : 330≤Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 330) hx
  have hh := density_height_parameters (k:=(1/3:ℝ)) hx0
    (by linarith) (by norm_num) (by linarith)
  obtain ⟨t,ht,hf⟩ := direct_lambda_finite hs hh.1 hh.2.1 hh.2.2.1 (by linarith)
  have hp := coefficient_of_finite hs h hRH hqrh
    (by decide : 0<(65536:ℕ)) hx (by
      refine ⟨t,?_,hf⟩
      simpa only [add_sub_cancel_right,sub_zero] using ht)
  have hb := hp.trans PVEvolutionA.SlopedRay330.coefficient
  rw [show -(1:ℝ)/8=-((1:ℝ)/8) by ring,Real.rpow_neg hx0.le]
  exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hx0 _)).mpr hb

/-- Actual consumer using the old unchanged numerical cap. -/
theorem psi330 (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    IEANTN.Eψ x≤(9150520022/1000000000000:ℝ)*x^(-(1:ℝ)/8) := by
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  have hL : 330≤Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 330) hx
  have hh := density_height_parameters (k:=(1/3:ℝ)) hx0
    (by linarith) (by norm_num) (by linarith)
  obtain ⟨t,ht,hf⟩ := raw_finite_transfer hs.hfe hs.hdig hs.h24u hs.h24l hs.hk
    hs.hneg hs.h2v hs.hv hs.hcs hs.hrvm hs.hsmall hs.hlow hs.hH
    (by convert hh.1 using 1 <;> norm_num [H]) hh.2.1 hh.2.2.1 (by linarith)
  have hp := coefficient_of_finite hs h hRH hqrh
    (by decide : 0<(65536:ℕ)) hx (by
      refine ⟨t,?_,hf⟩
      simpa only [add_sub_cancel_right,sub_zero] using ht)
  have hb := hp.trans PVEvolutionA.SlopedRay330.coefficient
  rw [show -(1:ℝ)/8=-((1:ℝ)/8) by ring,Real.rpow_neg hx0.le]
  exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hx0 _)).mpr hb

#print axioms coefficient_of_finite
#print axioms lambda330
#print axioms psi330
end E1FrozenN
