/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.OldTrunc
import PVCore.Decimal

/-!
# The three-cell QRH-free transport with no native fact

The kernel route of `KernelOnly.lean`, for the control configuration `OldTrunc` (FKS2 Table 3
step profile, cells `[300, 328]`, `[328, 329]`, `[329, 330]`): literal decoding by
`PVCore.decode_of_decodeL`, the shared-contract check on the decoded values, the cell and constant
certificates, each `decide +kernel`. It proves the registered `FKS2Numerics.v6.old_pi`.
-/

namespace Table4Evolution.OldTrunc.Kernel

open Real IEANTN PVCore Table4Evolution Table4Evolution.OldTrunc

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem decode_k : decode program =
    some (xsQ, 1 / 2 ^ 48, [(.plus, anchorQ), (.plus, pointQ), (.plus, tailQ)]) :=
  decode_of_decodeL (by decide +kernel)

theorem upper_k : upperFrom source program (4 / 10 ^ 27) (169 / 10 ^ 14) xsQ (1 / 2 ^ 48)
    [(.plus, anchorQ), (.plus, pointQ), (.plus, tailQ)] = true := by
  decide +kernel

theorem cells_k : cellsOK 0 48 stepM bs xsQ = true := by
  decide +kernel

theorem const_k : constOK 0 (stepM 300) (stepM 330) anchorQ pointQ tailQ = true := by
  decide +kernel

/-- The shared-contract certificate of the actual C file, assembled in the kernel. -/
theorem certificate_k : upperCheck source program (4 / 10 ^ 27) (169 / 10 ^ 14) = true :=
  (upperCheck_of_decode decode_k upper_k).1

/-- `FKS2Numerics.v6.old_pi`, kernel only. -/
theorem old_pi (h300 : FKS2.v8.table3_theta_300) (h310 : FKS2.v8.table3_theta_310)
    (h320 : FKS2.v8.table3_theta_320) (h330 : FKS2.v8.table3_theta_330)
    (hAnchor : FKS2.v6.table4_anchor_300) : FKS2Numerics.v6.old_pi := by
  obtain ⟨-, hx, hs, ho⟩ := upperCheck_of_decode decode_k upper_k
  have hb := program_bound certificate_k hs ho
  rw [hx] at hb
  have h := pi_bound (rest := [328, 329, 330]) (profile_step h300 h310 h320 h330) hAnchor cells_k
    (by decide) const_k hb
  show HasNumericalBound Eπ 1.69e-12 (exp 330)
  norm_num at h ⊢
  exact h

end Table4Evolution.OldTrunc.Kernel
