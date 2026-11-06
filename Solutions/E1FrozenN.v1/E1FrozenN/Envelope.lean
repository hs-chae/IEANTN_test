/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.Flexible
import PVEvolutionA.SlopedRayMid
/-! N analytic transport: numerical instances are inherited unchanged at00128.
No fresh program execution, array, profile or certificate is introduced. -/
namespace E1FrozenN
open Real Set MeasureTheory WinnerDensityA CH2QRH
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- Actual consumer using the old unchanged numerical cap. -/
theorem lambda_mid (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp (661/2:ℝ)≤x) :
    |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤(9145877463/1000000000000:ℝ)*x^(-(1:ℝ)/8) := by
  have hx0 : 0<x := (Real.exp_pos (661/2)).trans_le hx
  have hL : (661/2:ℝ)≤Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (661/2)) hx
  have hh := density_height_parameters (k:=(1/3:ℝ)) hx0
    (by linarith) (by norm_num) (by linarith)
  obtain ⟨t,ht,hf⟩ := direct_lambda_finite hs hh.1 hh.2.1 hh.2.2.1 (by linarith)
  have hp := flexible_coefficient hs h hRH hqrh
    (by decide : 0<(65536:ℕ)) (by norm_num : (300:ℝ)≤661/2) hx (by
      refine ⟨t,?_,hf⟩
      simpa only [add_sub_cancel_right,sub_zero] using ht)
  have hb := hp.trans PVEvolutionA.SlopedRayMid.coefficient
  rw [show -(1:ℝ)/8=-((1:ℝ)/8) by ring,Real.rpow_neg hx0.le]
  exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hx0 _)).mpr hb

/-- Actual consumer using the old unchanged numerical cap. -/
theorem psi_mid (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp (661/2:ℝ)≤x) :
    IEANTN.Eψ x≤(9145877463/1000000000000:ℝ)*x^(-(1:ℝ)/8) := by
  have hx0 : 0<x := (Real.exp_pos (661/2)).trans_le hx
  have hL : (661/2:ℝ)≤Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (661/2)) hx
  have hh := density_height_parameters (k:=(1/3:ℝ)) hx0
    (by linarith) (by norm_num) (by linarith)
  obtain ⟨t,ht,hf⟩ := raw_finite_transfer hs.hfe hs.hdig hs.h24u hs.h24l hs.hk
    hs.hneg hs.h2v hs.hv hs.hcs hs.hrvm hs.hsmall hs.hlow hs.hH
    (by convert hh.1 using 1 <;> norm_num [H]) hh.2.1 hh.2.2.1 (by linarith)
  have hp := flexible_coefficient hs h hRH hqrh
    (by decide : 0<(65536:ℕ)) (by norm_num : (300:ℝ)≤661/2) hx (by
      refine ⟨t,?_,hf⟩
      simpa only [add_sub_cancel_right,sub_zero] using ht)
  have hb := hp.trans PVEvolutionA.SlopedRayMid.coefficient
  rw [show -(1:ℝ)/8=-((1:ℝ)/8) by ring,Real.rpow_neg hx0.le]
  exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hx0 _)).mpr hb


noncomputable def errorBound (x:ℝ) : ℝ :=
  min ((if Real.exp (661/2:ℝ)≤x then (9145877463/1000000000000:ℝ)
    else 9150520022/1000000000000)*x^(-(1:ℝ)/8))
    (PVEvolutionA.Separated.coefficient 65536 (Real.log x) 100*x^(-(1:ℝ)/8))

theorem baseline_pair (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    IEANTN.Eψ x≤errorBound x ∧
    |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤errorBound x := by
  have hx300 : Real.exp (300:ℝ)≤x :=
    (Real.exp_le_exp.mpr (by norm_num : (300:ℝ)≤330)).trans hx
  have hp := psi_pointwise hs h hRH hqrh hx300
  have hl := lambda_pointwise hs h hRH hqrh hx300
  unfold errorBound
  split_ifs with hm
  · exact ⟨le_min (psi_mid hs h hRH hqrh hm) hp,
      le_min (lambda_mid hs h hRH hqrh hm) hl⟩
  · exact ⟨le_min (psi330 hs h hRH hqrh hx) hp,
      le_min (lambda330 hs h hRH hqrh hx) hl⟩

theorem direct_coefficient_lt_flat :
    (9150520022/1000000000000:ℝ)<9*(9150520022/1000000000000:ℝ) := by norm_num

#print axioms baseline_pair
#print axioms lambda_mid
#print axioms psi_mid
end E1FrozenN
