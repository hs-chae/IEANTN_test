/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVCore.Bridge
import PVRamanujan.Family
import CalibrationPilot.NewChain

/-!
# The A→B′ chain as a composition of two shared-contract stages

The updated pilot chain (`CalibrationPilot.NewChain`) composes two executed programs:

* **stage A**, `calibration_deviation`: seven calibration pieces, scaled by 4096; its certified
  bound is `Δ = 0.0914`;
* **stage B′**, `ramanujan_epsilon_bound`: the Ramanujan budget at `(m, M, A, Y) =
  (0, 120 + Δ, 9400, 9401)`.

Before, each stage carried its own 99- or 122-line certificate file with 7 and 6 native facts.
Here each stage is one certificate on the shared contract, and the composition is three explicit
compatibility facts:

1. **A's output contract.** `stageA`: the seven calibration targets sum to at most `Δ`, from A's
   certificate through `PVCore.le_bound_of_check`. Nothing else of A is used downstream.
2. **The data link.** `link`: B′'s parameter `M` equals `120 + Δ` for A's certified `Δ`, a
   kernel-checked equality of rationals (`CalibrationPilot.NewChain.M_eq`). B′ cannot be fed a
   different number without this equality failing.
3. **B′'s input contract.** `stageB`: B′'s certificate at exactly those parameters, through the
   family theorem `PVRamanujan.budget_of_check`.

The analytic steps between and after the stages (`calibrated_pi`, `piInput_of_calibrated`,
`epsilon_shift_nonneg`, `gap_from_budget`) are reused unchanged. The chain theorem's axioms are
the three standard ones plus two native facts, one per executed program.
-/

namespace PVPilot.Updated

open Real PVCore CalibrationPilot

/-- Stage A: the selected calibration program. -/
def programA : Program :=
  ⟨"calibration_deviation", NewA.literals, "4096.0", [(.minus, "0.0"), (.minus, "0.0")]⟩
def sourceA : String :=
  include_str ".." / ".." / "agentB-calibration" / "c" / "calibration_new.c"

/-- What the chain needs from stage A's certificate. Any proof of it will do: the native one
below, or the kernel one in `PVReplay.KernelChain` (decoding native, the rest kernel-checked). -/
abbrev CertA : Prop := upperCheck sourceA programA (1 / 10 ^ 10) NewA.bound = true ∧
    (valuesOf programA).ops = [(.minus, 0), (.minus, 0)] ∧
    NewA.targets.sum ≤ (valuesOf programA).scale * (valuesOf programA).xs.sum

theorem certificateA : CertA := by
  native_decide

/-- A's output contract: its seven pieces sum to at most its certified `Δ`. -/
theorem stageA_of (hA : CertA) : ((NewA.targets.sum : ℚ) : ℝ) ≤ ((NewA.bound : ℚ) : ℝ) := by
  apply le_bound_of_check hA.1
  rw [hA.2.1]
  have h := hA.2.2
  simp only [opsConst, neg_zero, add_zero, Rat.cast_zero]
  exact_mod_cast h

theorem stageA : ((NewA.targets.sum : ℚ) : ℝ) ≤ ((NewA.bound : ℚ) : ℝ) := stageA_of certificateA

/-- Stage B′: the selected Ramanujan budget program at the linked parameters. -/
def programB : Program := PVRamanujan.program NewB.literals "4096.0" "134.0" "0.0"
def sourceB : String :=
  include_str ".." / ".." / "agentB-calibration" / "c" / "ramanujan_9401_new.c"

/-- What the chain needs from stage B′'s certificate. -/
abbrev CertB : Prop :=
  PVRamanujan.budgetCheck sourceB programB NewB.m NewB.M NewB.A NewB.Y (1 / 10 ^ 10) NewB.bound =
    true

theorem certificateB : CertB := by
  native_decide

/-- B′'s input contract at exactly the parameters it was certified for. -/
theorem stageB_of (hB : CertB) : ∀ x > exp ((NewB.Y : ℚ) : ℝ),
    DudekPlatt.v3.εUpper ((NewB.M : ℚ) : ℝ) x -
      DudekPlatt.v3.εLower ((NewB.m : ℚ) : ℝ) (exp ((NewB.A : ℚ) : ℝ)) x ≤ ((NewB.bound : ℚ) : ℝ) :=
  PVRamanujan.budget_of_check hB

theorem stageB : ∀ x > exp ((NewB.Y : ℚ) : ℝ), DudekPlatt.v3.εUpper ((NewB.M : ℚ) : ℝ) x -
    DudekPlatt.v3.εLower ((NewB.m : ℚ) : ℝ) (exp ((NewB.A : ℚ) : ℝ)) x ≤ ((NewB.bound : ℚ) : ℝ) :=
  stageB_of certificateB

/-- The data link from A to B′: B′'s `M` is `120 + Δ` for A's certified `Δ`. -/
theorem link : ((NewB.M : ℚ) : ℝ) = 120 + ((NewA.bound : ℚ) : ℝ) := NewChain.M_eq

theorem deviation_of (hA : CertA) :
    1 / 10 ^ 12 + dPiece (1 / 10 ^ 12) 9400 + iPiece 9400 + aPiece 9400 < NewChain.Δ := by
  have h := stageA_of hA
  rw [NewChain.targets_eq] at h
  exact NewInput.deviation_lt_targets.trans_le h

theorem pi_input_of (hA : CertA) (hpsi : QRHCH2.v5.psi_refined_bound) :
    ForwardRamanujan.PiInput NewChain.m (NewB.M : ℝ) (NewB.A : ℝ) := by
  rw [link, NewChain.A_eq]
  exact piInput_of_calibrated (calibrated_pi DudekPlattNumerics.v4.Numerics.hlog2_proof
    (le_refl _) (by norm_num) (NewInput.point hpsi) (NewInput.tail hpsi) (deviation_of hA))

theorem budget_of (hB : CertB) : ∀ x > exp 9401, DudekPlatt.v3.εUpper (NewB.M : ℝ) x -
    DudekPlatt.v3.εLower NewChain.m (exp (NewB.A : ℝ)) x ≤ NewChain.C := by
  intro x hx
  have hx' : exp ((NewB.Y : ℚ) : ℝ) < x := by rw [NewChain.Y_eq]; exact hx
  have hb := stageB_of hB x hx'
  rw [NewChain.mB_eq] at hb
  have hm : 0 ≤ NewChain.m := by rw [NewChain.m_val]; norm_num
  exact epsilon_shift_nonneg hm hb

/-- The chain, for any proofs of the two stage certificates. -/
theorem gap_of (hA : CertA) (hB : CertB) (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ x > exp 9401,
      (1 + (68431 / 5000) / log x) * x ^ 2 / log x ^ 6 < ForwardRamanujan.gap x := by
  intro x hx
  have hx' : exp ((NewB.Y : ℚ) : ℝ) < x := by rw [NewChain.Y_eq]; exact hx
  have hg := ForwardRamanujan.gap_from_budget (by rw [NewChain.A_eq]; norm_num)
    (by rw [NewChain.A_eq, NewChain.Y_eq]; norm_num) (pi_input_of hA hpsi) hx' (budget_of hB x hx)
  have hL : 0 < log x := by
    have := log_lt_log (exp_pos _) hx
    rw [log_exp] at this
    linarith
  rw [NewChain.C_val] at hg
  convert hg using 1
  field_simp
  ring

theorem deviation :
    1 / 10 ^ 12 + dPiece (1 / 10 ^ 12) 9400 + iPiece 9400 + aPiece 9400 < NewChain.Δ :=
  deviation_of certificateA

/-- **Chain theorem.** On `x > e^9401`, the Ramanujan gap exceeds its leading term by
`13.6862/log x` in relative size, from the QRH-derived θ input through both executed stages. -/
theorem gap_exceeds_leading (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ x > exp 9401,
      (1 + (68431 / 5000) / log x) * x ^ 2 / log x ^ 6 < ForwardRamanujan.gap x :=
  gap_of certificateA certificateB hpsi

end PVPilot.Updated
