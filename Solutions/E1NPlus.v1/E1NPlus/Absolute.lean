/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.Final
import PVEvolutionA.SlopedRay300
namespace E1NPlus
open Real Set E1FrozenN WinnerDensityA CH2QRH
set_option maxHeartbeats 0

section Inputs
variable (hs:E1FrozenN.DirectCH2Inputs)
  (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
  (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
  (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
include hs h hRH hQRH

theorem psi_grid {n:ℕ} (hn:0<n) {L0 x:ℝ} (h0:300 ≤ L0) (hx:exp L0 ≤ x) :
    IEANTN.Eψ x ≤ PVEvolutionA.Separated.coefficient n L0 100*x^(-(1:ℝ)/8) := by
  have hx0:0<x:=(exp_pos _).trans_le hx
  have hL:L0 ≤ log x:=by simpa only [log_exp] using log_le_log (exp_pos _) hx
  have hh:=density_height_parameters (k:=(1/3:ℝ)) hx0 (by linarith) (by norm_num) (by linarith)
  obtain ⟨t,ht,hf⟩:=raw_finite_transfer hs.hfe hs.hdig hs.h24u hs.h24l hs.hk
    hs.hneg hs.h2v hs.hv hs.hcs hs.hrvm hs.hsmall hs.hlow hs.hH
    (by convert hh.1 using 1 <;> norm_num [H]) hh.2.1 hh.2.2.1 (by linarith)
  have hp:=flexible_coefficient hs h hRH hQRH hn h0 hx (by
    refine ⟨t,?_,hf⟩
    simpa only [add_sub_cancel_right,sub_zero] using ht)
  rw [show -(1:ℝ)/8=-((1:ℝ)/8) by ring,rpow_neg hx0.le]
  exact (le_mul_inv_iff₀ (rpow_pos_of_pos hx0 _)).mpr hp

theorem lambda_grid {n:ℕ} (hn:0<n) {L0 x:ℝ} (h0:300 ≤ L0) (hx:exp L0 ≤ x) :
    |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤
      PVEvolutionA.Separated.coefficient n L0 100*x^(-(1:ℝ)/8) := by
  have hx0:0<x:=(exp_pos _).trans_le hx
  have hL:L0 ≤ log x:=by simpa only [log_exp] using log_le_log (exp_pos _) hx
  have hh:=density_height_parameters (k:=(1/3:ℝ)) hx0 (by linarith) (by norm_num) (by linarith)
  obtain ⟨t,ht,hf⟩:=direct_lambda_finite hs hh.1 hh.2.1 hh.2.2.1 (by linarith)
  have hp:=flexible_coefficient hs h hRH hQRH hn h0 hx (by
    refine ⟨t,?_,hf⟩
    simpa only [add_sub_cancel_right,sub_zero] using ht)
  rw [show -(1:ℝ)/8=-((1:ℝ)/8) by ring,rpow_neg hx0.le]
  exact (le_mul_inv_iff₀ (rpow_pos_of_pos hx0 _)).mpr hp

theorem pair300 {x:ℝ} (hx:exp (300:ℝ) ≤ x) :
    IEANTN.Eψ x ≤ (9468285637/1000000000000:ℝ)*x^(-(1:ℝ)/8) ∧
    |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤
      (9468285637/1000000000000:ℝ)*x^(-(1:ℝ)/8) := by
  have hsx:=mul_le_mul_of_nonneg_right PVEvolutionA.SlopedRay300.coefficient
    (rpow_nonneg ((exp_pos _).trans_le hx).le (-(1:ℝ)/8))
  exact ⟨(psi_grid hs h hRH hQRH (by decide : 0<(65536:ℕ)) (by norm_num) hx).trans hsx,
    (lambda_grid hs h hRH hQRH (by decide : 0<(65536:ℕ)) (by norm_num) hx).trans hsx⟩
end Inputs

/-- The infimum over every symbolic grid resolution, with no new execution. -/
noncomputable def gridInfBound (x:ℝ):ℝ:=
  ⨅n:ℕ+,PVEvolutionA.Separated.coefficient (n:ℕ) (log x) 100*x^(-(1:ℝ)/8)

section Inputs
variable (hs:E1FrozenN.DirectCH2Inputs)
  (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
  (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
  (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
include hs h hRH hQRH

theorem grid_family_bddBelow {x:ℝ} (hx:exp (300:ℝ) ≤ x) :
    BddBelow (Set.range (fun n:ℕ+↦PVEvolutionA.Separated.coefficient (n:ℕ) (log x) 100*x^(-(1:ℝ)/8))) := by
  have hx0:0<x:=(exp_pos _).trans_le hx
  have hL:300 ≤ log x:=by simpa only [log_exp] using log_le_log (exp_pos _) hx
  refine ⟨IEANTN.Eψ x,?_⟩
  rintro y ⟨n,rfl⟩
  exact psi_grid hs h hRH hQRH n.pos hL (le_of_eq (exp_log hx0))

theorem pair_grid_inf {x:ℝ} (hx:exp (300:ℝ) ≤ x) :
    IEANTN.Eψ x ≤ gridInfBound x ∧
    |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤ gridInfBound x := by
  have hx0:0<x:=(exp_pos _).trans_le hx
  have hL:300 ≤ log x:=by simpa only [log_exp] using log_le_log (exp_pos _) hx
  constructor
  · apply le_ciInf
    intro n
    exact psi_grid hs h hRH hQRH n.pos hL (le_of_eq (exp_log hx0))
  · apply le_ciInf
    intro n
    exact lambda_grid hs h hRH hQRH n.pos hL (le_of_eq (exp_log hx0))
end Inputs
#print axioms pair300
#print axioms pair_grid_inf
end E1NPlus
