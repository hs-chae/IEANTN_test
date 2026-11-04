/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude), integration workstream
-/
import CalibrationPilot.NewInput
import CalibrationPilot.NewA
import CalibrationPilot.NewB
import CalibrationPilot.OldChain
import IEANTN.Nodes.RamanujanGap.v2.Conclusions

/-!
# Updated chain: QRH-derived theta bound → program A → π expansion → program B′ → gap

Same generic adapter, same program shapes, same frozen soundness theorems as the old chain
(`OldChain`, frozen at commit `caf4013`). What changed:
- program A's input data: two of its seven literals, the theta point and tail entries;
- the analytic adapter `NewInput`, because the QRH bound has a different shape from MT's;
- program B′'s data and certificate.

Program A now certifies `Δ = 0.0914`, so the coefficients are `(m, M) = (119.9086, 120.0914)`.
`m` is positive, and program B's frozen family needs a positive output. B′ is therefore run at
`m = 0`, and `epsilon_shift_nonneg` subtracts `m` in exact arithmetic. The resulting budget is
negative, `C = 106.2224 − 119.9086 = −13.6862`. So on `x > e^9401` the gap exceeds its leading term:
`gap(x) > (1 + 13.6862/log x) · x²/(log x)⁶`.
-/

namespace CalibrationPilot.NewChain
open Real CalibrationPilot

theorem targets_eq : CalibrationPilot.NewA.targets = CalibrationPilot.NewInput.targets := by
  simp only [CalibrationPilot.NewA.targets, CalibrationPilot.NewInput.targets]
  norm_num

noncomputable def Δ : ℝ := (CalibrationPilot.NewA.bound : ℝ)

theorem deviation : 1 / 10 ^ 12 + dPiece (1 / 10 ^ 12) 9400 + iPiece 9400 + aPiece 9400 < Δ := by
  have h := CalibrationPilot.NewA.certified_sum
  rw [targets_eq] at h
  exact CalibrationPilot.NewInput.deviation_lt_targets.trans_le h

theorem pi_calibrated (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ x > exp 9400,
      DudekPlatt.v3.mainTerm x + (120 - Δ) * x / log x ^ 6 < IEANTN.primeCounting x ∧
        IEANTN.primeCounting x < DudekPlatt.v3.mainTerm x + (120 + Δ) * x / log x ^ 6 :=
  calibrated_pi DudekPlattNumerics.v4.Numerics.hlog2_proof (le_refl _) (by norm_num)
    (CalibrationPilot.NewInput.point hpsi) (CalibrationPilot.NewInput.tail hpsi) deviation

/-- Lower coefficient, exact. -/
noncomputable def m : ℝ := 120 - Δ

theorem m_val : m = 599543 / 5000 := by
  simp only [m, Δ, CalibrationPilot.NewA.bound]
  norm_num

theorem M_eq : ((CalibrationPilot.NewB.M : ℚ) : ℝ) = 120 + Δ := by
  simp only [Δ, CalibrationPilot.NewB.M, CalibrationPilot.NewA.bound]
  norm_num

theorem mB_eq : ((CalibrationPilot.NewB.m : ℚ) : ℝ) = 0 := by
  simp only [CalibrationPilot.NewB.m]
  norm_num

theorem A_eq : ((CalibrationPilot.NewB.A : ℚ) : ℝ) = 9400 := by
  simp only [CalibrationPilot.NewB.A]
  norm_num

theorem Y_eq : ((CalibrationPilot.NewB.Y : ℚ) : ℝ) = 9401 := by
  simp only [CalibrationPilot.NewB.Y]
  norm_num

theorem pi_input (hpsi : QRHCH2.v5.psi_refined_bound) :
    ForwardRamanujan.PiInput m (CalibrationPilot.NewB.M : ℝ) (CalibrationPilot.NewB.A : ℝ) := by
  rw [M_eq, A_eq]
  exact piInput_of_calibrated (pi_calibrated hpsi)

/-- The budget after the exact shift: `C = bound(B′ at m = 0) − m`. -/
noncomputable def C : ℝ := (CalibrationPilot.NewB.bound : ℝ) - m

theorem C_val : C = -(68431 / 5000) := by
  simp only [C, m_val, CalibrationPilot.NewB.bound]
  norm_num

theorem budget : ∀ x > exp 9401,
    DudekPlatt.v3.εUpper (CalibrationPilot.NewB.M : ℝ) x -
      DudekPlatt.v3.εLower m (exp (CalibrationPilot.NewB.A : ℝ)) x ≤ C := by
  intro x hx
  have hx' : exp ((CalibrationPilot.NewB.Y : ℚ) : ℝ) < x := by rw [Y_eq]; exact hx
  have hb := CalibrationPilot.NewB.epsilon_bound x hx'
  rw [mB_eq] at hb
  have hm : 0 ≤ m := by rw [m_val]; norm_num
  exact epsilon_shift_nonneg hm hb

theorem gap_bound (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ x > exp 9401, x ^ 2 * ((log x - C) / log x ^ 7) < ForwardRamanujan.gap x := by
  intro x hx
  have hx' : exp ((CalibrationPilot.NewB.Y : ℚ) : ℝ) < x := by rw [Y_eq]; exact hx
  exact ForwardRamanujan.gap_from_budget (by rw [A_eq]; norm_num) (by rw [A_eq, Y_eq]; norm_num)
    (pi_input hpsi) hx' (budget x hx)

/-- The gap exceeds its leading term by `13.6862/log x` in relative size. -/
theorem gap_exceeds_leading (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ x > exp 9401,
      (1 + (68431 / 5000) / log x) * x ^ 2 / log x ^ 6 < ForwardRamanujan.gap x := by
  intro x hx
  have hg := gap_bound hpsi x hx
  have hL : 0 < log x := by
    have := log_lt_log (exp_pos _) hx
    rw [log_exp] at this
    linarith
  rw [C_val] at hg
  convert hg using 1
  field_simp
  ring

theorem loss_zero (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ x > exp 9401, ForwardRamanujan.loss x = 0 := by
  intro x hx
  have hx' : exp ((CalibrationPilot.NewB.Y : ℚ) : ℝ) < x := by rw [Y_eq]; exact hx
  have hC : C ≤ 0 := by rw [C_val]; norm_num
  have h := ForwardRamanujan.loss_from_budget (C := 0) (by rw [A_eq]; norm_num)
    (by rw [A_eq, Y_eq]; norm_num) (pi_input hpsi) (le_refl 0) hx'
    ((budget x hx).trans hC)
  have h0 : 0 ≤ ForwardRamanujan.loss x := le_max_left _ _
  rw [zero_div] at h
  linarith

/-- On the matched sub-ray `x > e^9401`, the network's existing QRH Ramanujan consequence
(`RamanujanGap.v2.gap_lower_bound`, allowance `9.101`) is strictly weaker than this chain's. Only
certified lower bounds are compared, not true errors. -/
theorem stronger_than_v2_on_subray :
    ∀ x > exp 9401, (1 - RamanujanNumerics.v2.allowance / log x) * x ^ 2 / log x ^ 6 <
      (1 + (68431 / 5000) / log x) * x ^ 2 / log x ^ 6 := by
  intro x hx
  have hL : 0 < log x := by
    have := log_lt_log (exp_pos _) hx
    rw [log_exp] at this
    linarith
  have hx0 : 0 < x := (exp_pos _).trans hx
  have hw : 0 < x ^ 2 / log x ^ 6 := by positivity
  have h1 : 1 - RamanujanNumerics.v2.allowance / log x < 1 + (68431 / 5000) / log x := by
    have : 0 < RamanujanNumerics.v2.allowance / log x := by
      unfold RamanujanNumerics.v2.allowance
      positivity
    have : 0 < (68431 / 5000 : ℝ) / log x := by positivity
    linarith
  have e1 : (1 - RamanujanNumerics.v2.allowance / log x) * x ^ 2 / log x ^ 6 =
      (1 - RamanujanNumerics.v2.allowance / log x) * (x ^ 2 / log x ^ 6) := by ring
  have e2 : (1 + (68431 / 5000) / log x) * x ^ 2 / log x ^ 6 =
      (1 + (68431 / 5000) / log x) * (x ^ 2 / log x ^ 6) := by ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_right h1 hw

theorem ramanujan_9401 (hpsi : QRHCH2.v5.psi_refined_bound) :
    DudekPlatt.v4.ramanujan_inequality_9401 := by
  intro x hx
  have hg := gap_exceeds_leading hpsi x hx
  have hL : 0 < log x := by
    have := log_lt_log (exp_pos _) hx
    rw [log_exp] at this
    linarith
  have hpos : 0 ≤ (1 + (68431 / 5000) / log x) * x ^ 2 / log x ^ 6 := by positivity
  have := hpos.trans_lt hg
  unfold ForwardRamanujan.gap at this
  linarith

/-- **The updated A → B chain**, every executed program consumed. -/
theorem new_chain (hpsi : QRHCH2.v5.psi_refined_bound) :
    (∀ x > exp 9400,
      DudekPlatt.v3.mainTerm x + (120 - Δ) * x / log x ^ 6 < IEANTN.primeCounting x ∧
        IEANTN.primeCounting x < DudekPlatt.v3.mainTerm x + (120 + Δ) * x / log x ^ 6) ∧
    (∀ x > exp 9401,
      (1 + (68431 / 5000) / log x) * x ^ 2 / log x ^ 6 < ForwardRamanujan.gap x) ∧
    (∀ x > exp 9401, ForwardRamanujan.loss x = 0) ∧
    DudekPlatt.v4.ramanujan_inequality_9401 :=
  ⟨pi_calibrated hpsi, gap_exceeds_leading hpsi, loss_zero hpsi, ramanujan_9401 hpsi⟩

/-- Both configurations side by side: the old chain still holds unchanged under its own premise. -/
theorem paired (hMT : MT.v2.corollary_1) (hpsi : QRHCH2.v5.psi_refined_bound) :
    (∀ x > exp 9401, ForwardRamanujan.loss x ≤ CalibrationPilot.OldChain.C / log x) ∧
    (∀ x > exp 9401, ForwardRamanujan.loss x = 0) :=
  ⟨CalibrationPilot.OldChain.loss_bound hMT, loss_zero hpsi⟩

end CalibrationPilot.NewChain
