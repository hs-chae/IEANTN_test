/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude), integration workstream
-/
import CalibrationPilot.KernelA
import CalibrationPilot.NewChain

/-!
# The updated chain with the kernel-reduced program A

Same statement as `NewChain.pi_calibrated` and `NewChain.new_chain`. Program A's certificate now
carries one native fact, literal decoding, instead of seven. Program B′ is unchanged and still
carries six.
-/

namespace CalibrationPilot.KernelChain
open Real CalibrationPilot

theorem deviation_k :
    1 / 10 ^ 12 + dPiece (1 / 10 ^ 12) 9400 + iPiece 9400 + aPiece 9400 < NewChain.Δ := by
  have h := CalibrationPilot.KernelA.certified_sum_k
  rw [NewChain.targets_eq] at h
  exact CalibrationPilot.NewInput.deviation_lt_targets.trans_le h

theorem pi_calibrated_k (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ x > exp 9400,
      DudekPlatt.v3.mainTerm x + (120 - NewChain.Δ) * x / log x ^ 6 < IEANTN.primeCounting x ∧
        IEANTN.primeCounting x < DudekPlatt.v3.mainTerm x + (120 + NewChain.Δ) * x / log x ^ 6 :=
  calibrated_pi DudekPlattNumerics.v4.Numerics.hlog2_proof (le_refl _) (by norm_num)
    (CalibrationPilot.NewInput.point hpsi) (CalibrationPilot.NewInput.tail hpsi) deviation_k

end CalibrationPilot.KernelChain
