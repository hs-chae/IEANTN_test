/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.AbsoluteFinal
namespace E1NPlus
open Real Set E1FrozenN WinnerDensityA CH2QRH
set_option maxHeartbeats 0
theorem lambda_tight_all (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {n:ℕ} (hn:0<n) {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤(PVEvolutionA.Separated.coefficient n 330 100-1/10^12+1/10^28:ℝ)*x^(-(1:ℝ)/8) := by
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  have hL : 330≤Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 330) hx
  have hh := density_height_parameters (k:=(1/3:ℝ)) hx0
    (by linarith) (by norm_num) (by linarith)
  obtain ⟨t,ht,hf⟩ := direct_lambda_finite hs hh.1 hh.2.1 hh.2.2.1 (by linarith)
  have hp := tight_coefficient_of_finite hs h hRH hqrh
    hn hx (by
      refine ⟨t,?_,hf⟩
      simpa only [add_sub_cancel_right,sub_zero] using ht)
  rw [show -(1:ℝ)/8=-((1:ℝ)/8) by ring,Real.rpow_neg hx0.le]
  exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hx0 _)).mpr hp

theorem psi_tight_all (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {n:ℕ} (hn:0<n) {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    IEANTN.Eψ x≤(PVEvolutionA.Separated.coefficient n 330 100-1/10^12+1/10^28:ℝ)*x^(-(1:ℝ)/8) := by
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  have hL : 330≤Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 330) hx
  have hh := density_height_parameters (k:=(1/3:ℝ)) hx0
    (by linarith) (by norm_num) (by linarith)
  obtain ⟨t,ht,hf⟩ := raw_finite_transfer hs.hfe hs.hdig hs.h24u hs.h24l hs.hk
    hs.hneg hs.h2v hs.hv hs.hcs hs.hrvm hs.hsmall hs.hlow hs.hH
    (by convert hh.1 using 1 <;> norm_num [H]) hh.2.1 hh.2.2.1 (by linarith)
  have hp := tight_coefficient_of_finite hs h hRH hqrh
    hn hx (by
      refine ⟨t,?_,hf⟩
      simpa only [add_sub_cancel_right,sub_zero] using ht)
  rw [show -(1:ℝ)/8=-((1:ℝ)/8) by ring,Real.rpow_neg hx0.le]
  exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hx0 _)).mpr hp
noncomputable def tightInfBound (x:ℝ):ℝ:=
  ⨅n:ℕ+,(PVEvolutionA.Separated.coefficient (n:ℕ) 330 100-1/10^12+1/10^28)*x^(-(1:ℝ)/8)
noncomputable def finalPairBound (x:ℝ):ℝ:=min (pairBound x)
  (if exp (330:ℝ) ≤ x then tightInfBound x else pairBound x)
theorem final_pair (hs:DirectCH2Inputs)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:exp (300:ℝ) ≤ x):
    IEANTN.Eψ x ≤ finalPairBound x ∧
    |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤ finalPairBound x := by
  have hp:=pair_full hs h hRH hQRH hx
  by_cases h330:exp (330:ℝ) ≤ x
  · have ht:IEANTN.Eψ x ≤ tightInfBound x:=le_ciInf (fun n=>psi_tight_all hs h hRH hQRH n.pos h330)
    have hw:|CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤ tightInfBound x:=
      le_ciInf (fun n=>lambda_tight_all hs h hRH hQRH n.pos h330)
    exact ⟨le_min hp.1 (by simpa [h330] using ht),le_min hp.2 (by simpa [h330] using hw)⟩
  · simpa [finalPairBound,h330] using hp
#print axioms final_pair
end E1NPlus
