/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude), integration workstream
-/
import CalibrationPilot.OldInput
import CalibrationPilot.OldA
import CalibrationPilot.OldB
import IEANTN.Nodes.DudekPlatt.v4.Conclusions
import IEANTN.Nodes.DudekPlattNumerics.v4.Conclusions

/-!
# Old chain: `MT.v2.corollary_1` → program A → π expansion → program B′ → Ramanujan gap

Both executed programs are consumed in the proof body: program A's `certified_sum` supplies the
calibration constant `Δ = 3110.5023`, and program B′'s `epsilon_bound` supplies the budget
`C = 9320.1177` for the calibrated coefficients `(m, M) = (120 − Δ, 120 + Δ)`.

The chain also re-derives two existing, Comparator-accepted node statements,
`DudekPlattNumerics.v4.pi_two_sided_footnote` and `DudekPlatt.v4.ramanujan_inequality_9401`.
It is an **alternative route with weaker trust** (12 native facts), not a replacement for them.
-/

namespace CalibrationPilot.OldChain
open Real CalibrationPilot

theorem targets_eq : CalibrationPilot.OldA.targets = CalibrationPilot.OldInput.targets := by
  simp only [CalibrationPilot.OldA.targets, CalibrationPilot.OldInput.targets]
  norm_num

/-- The calibration constant certified by program A. -/
noncomputable def Δ : ℝ := (CalibrationPilot.OldA.bound : ℝ)

theorem deviation : 3110 + dPiece 3600 9400 + iPiece 9400 + aPiece 9400 < Δ := by
  have h := CalibrationPilot.OldA.certified_sum
  rw [targets_eq] at h
  exact CalibrationPilot.OldInput.deviation_lt_targets.trans_le h

/-- Step A → π: the two-sided expansion with program A's coefficients, on every `x > exp 9400`. -/
theorem pi_calibrated (hMT : MT.v2.corollary_1) :
    ∀ x > exp 9400,
      DudekPlatt.v3.mainTerm x + (120 - Δ) * x / log x ^ 6 < IEANTN.primeCounting x ∧
        IEANTN.primeCounting x < DudekPlatt.v3.mainTerm x + (120 + Δ) * x / log x ^ 6 :=
  calibrated_pi DudekPlattNumerics.v4.Numerics.hlog2_proof (le_refl _) (by norm_num)
    (CalibrationPilot.OldInput.point hMT) (CalibrationPilot.OldInput.tail hMT) deviation

theorem m_eq : ((CalibrationPilot.OldB.m : ℚ) : ℝ) = 120 - Δ := by
  simp only [Δ, CalibrationPilot.OldB.m, CalibrationPilot.OldA.bound]
  norm_num

theorem M_eq : ((CalibrationPilot.OldB.M : ℚ) : ℝ) = 120 + Δ := by
  simp only [Δ, CalibrationPilot.OldB.M, CalibrationPilot.OldA.bound]
  norm_num

theorem A_eq : ((CalibrationPilot.OldB.A : ℚ) : ℝ) = 9400 := by
  simp only [CalibrationPilot.OldB.A]
  norm_num

theorem Y_eq : ((CalibrationPilot.OldB.Y : ℚ) : ℝ) = 9401 := by
  simp only [CalibrationPilot.OldB.Y]
  norm_num

/-- Step π → B′ input: program B's frozen input shape, at the calibrated coefficients. -/
theorem pi_input (hMT : MT.v2.corollary_1) :
    ForwardRamanujan.PiInput (CalibrationPilot.OldB.m : ℝ) (CalibrationPilot.OldB.M : ℝ)
      (CalibrationPilot.OldB.A : ℝ) := by
  rw [m_eq, M_eq, A_eq]
  exact piInput_of_calibrated (pi_calibrated hMT)

/-- The budget `C` certified by program B′. -/
noncomputable def C : ℝ := (CalibrationPilot.OldB.bound : ℝ)

theorem C_lt : C < 9401 := by
  simp only [C, CalibrationPilot.OldB.bound]
  norm_num

theorem C_nonneg : 0 ≤ C := by
  simp only [C, CalibrationPilot.OldB.bound]
  norm_num

/-- Step B′ → gap: the quantitative Ramanujan consequence on `x > exp 9401`. -/
theorem gap_bound (hMT : MT.v2.corollary_1) :
    ∀ x > exp 9401, x ^ 2 * ((log x - C) / log x ^ 7) < ForwardRamanujan.gap x := by
  intro x hx
  have hx' : exp ((CalibrationPilot.OldB.Y : ℚ) : ℝ) < x := by rw [Y_eq]; exact hx
  have hb := CalibrationPilot.OldB.epsilon_bound x hx'
  exact ForwardRamanujan.gap_from_budget (by rw [A_eq]; norm_num) (by rw [A_eq, Y_eq]; norm_num)
    (pi_input hMT) hx' hb

theorem loss_bound (hMT : MT.v2.corollary_1) :
    ∀ x > exp 9401, ForwardRamanujan.loss x ≤ C / log x := by
  intro x hx
  have hx' : exp ((CalibrationPilot.OldB.Y : ℚ) : ℝ) < x := by rw [Y_eq]; exact hx
  have hb := CalibrationPilot.OldB.epsilon_bound x hx'
  exact ForwardRamanujan.loss_from_budget (by rw [A_eq]; norm_num) (by rw [A_eq, Y_eq]; norm_num)
    (pi_input hMT) C_nonneg hx' hb

/-- Re-derivation of the existing node statement (accepted route untouched). -/
theorem ramanujan_9401 (hMT : MT.v2.corollary_1) : DudekPlatt.v4.ramanujan_inequality_9401 := by
  intro x hx
  have hg := gap_bound hMT x hx
  have hL : 9401 < log x := by
    have := log_lt_log (exp_pos _) hx
    rwa [log_exp] at this
  have hpos : 0 ≤ x ^ 2 * ((log x - C) / log x ^ 7) := by
    have := C_lt
    have hl : 0 < log x := by linarith
    apply mul_nonneg (sq_nonneg x)
    apply div_nonneg (by linarith) (by positivity)
  have := hg.trans_le' hpos
  unfold ForwardRamanujan.gap at this
  linarith

/-- Re-derivation of the existing node statement, with A's (stronger) coefficients weakened to
the published ones. -/
theorem footnote (hMT : MT.v2.corollary_1) : DudekPlattNumerics.v4.pi_two_sided_footnote := by
  intro x hx
  have h := pi_calibrated hMT x hx
  have hx0 : 0 < x := (exp_pos _).trans hx
  have hL : 9400 < log x := by
    have := log_lt_log (exp_pos _) hx
    rwa [log_exp] at this
  have hw : 0 < x / log x ^ 6 := by
    have : 0 < log x := by linarith
    positivity
  have hΔ1 : 120 - Δ = -(29905023 / 10000 : ℝ) := by
    simp only [Δ, CalibrationPilot.OldA.bound]; norm_num
  have hΔ2 : 120 + Δ = (32305023 / 10000 : ℝ) := by
    simp only [Δ, CalibrationPilot.OldA.bound]; norm_num
  rw [hΔ1, hΔ2] at h
  simp only [DudekPlattNumerics.v4.mainTerm, IEANTN.margin, pow_zero, one_mul]
  change DudekPlatt.v3.mainTerm x - _ < _ ∧ _ < DudekPlatt.v3.mainTerm x + _
  constructor
  · have e : -(29905023 / 10000 : ℝ) * x / log x ^ 6 = -(29905023 / 10000) * (x / log x ^ 6) := by
      ring
    nlinarith [h.1]
  · have e : (32305023 / 10000 : ℝ) * x / log x ^ 6 = (32305023 / 10000) * (x / log x ^ 6) := by
      ring
    nlinarith [h.2]

/-- **The old A → B chain**, every executed program consumed. -/
theorem old_chain (hMT : MT.v2.corollary_1) :
    (∀ x > exp 9400,
      DudekPlatt.v3.mainTerm x + (120 - Δ) * x / log x ^ 6 < IEANTN.primeCounting x ∧
        IEANTN.primeCounting x < DudekPlatt.v3.mainTerm x + (120 + Δ) * x / log x ^ 6) ∧
    (∀ x > exp 9401, ForwardRamanujan.loss x ≤ C / log x) ∧
    (∀ x > exp 9401, x ^ 2 * ((log x - C) / log x ^ 7) < ForwardRamanujan.gap x) ∧
    DudekPlatt.v4.ramanujan_inequality_9401 ∧ DudekPlattNumerics.v4.pi_two_sided_footnote :=
  ⟨pi_calibrated hMT, loss_bound hMT, gap_bound hMT, ramanujan_9401 hMT, footnote hMT⟩

end CalibrationPilot.OldChain
