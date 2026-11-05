/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVReplay.Ramanujan
import PVCore.Kernel
import PVRamanujan.Kernel
import PVCore.Decimal

/-!
# The four Ramanujan-budget replays with no native fact

`PVReplay.Ramanujan` proves `RamanujanNumerics.v1.epsilon_budget`, `RamanujanNumerics.v2.epsilon_budget`
and the two grouped variants from one `native_decide` certificate each. Here each certificate is
assembled in the kernel: the literals of the selected C file are decoded by
`PVCore.decode_of_decodeL` (`decide +kernel`), and the budget check on the decoded values
(`PVRamanujan.budgetFrom`: token matching, the binary64 chain, the enclosure of the budget terms,
the forward-error bound) is `decide +kernel`. `PVRamanujan.budgetCheck_of_decode` turns the two into
the certificate the family theorem consumes. Same statements, same premises (none: these budgets are
unconditional numerical facts about the given coefficients).
-/

namespace PVRamanujan.KernelOnly

open Real PVCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace V1

/-- The seven literals of `RamanujanNumerics.v1`'s `baseline.c`, as exact binary64 values. -/
def xs : List ℚ := [713 / 1024, 3432628681500271 / 18446744073709551616,
  3605769814485911 / 37778931862957161709568, 87000777849225 / 1208925819614629174706176,
  1 / 1099511627776, 1 / 1099511627776, 1314830663393493 / 4503599627370496]

theorem decode_k :
    decode PVRamanujan.V1.program = some (xs, 4096, [(.minus, 134), (.minus, 0)]) :=
  decode_of_decodeL (by decide +kernel)

theorem budget_k : budgetFrom PVRamanujan.V1.source PVRamanujan.V1.program (-1194) 1426 3914 3915
    (1 / 10 ^ 10) (39147 / 10) xs 4096 [(.minus, 134), (.minus, 0)] = true := by
  decide +kernel

theorem certificate_k : budgetCheck PVRamanujan.V1.source PVRamanujan.V1.program (-1194) 1426 3914
    3915 (1 / 10 ^ 10) (39147 / 10) = true :=
  budgetCheck_of_decode decode_k budget_k

/-- `RamanujanNumerics.v1.epsilon_budget`, kernel only. -/
theorem epsilon_budget : RamanujanNumerics.v1.epsilon_budget := by
  intro x hx
  have h := budget_of_check certificate_k x (by simpa using hx)
  have hb : (((39147 / 10 : ℚ)) : ℝ) = 3914.7 := by norm_num
  rw [hb] at h
  simpa using h

end V1

namespace V2

/-- The seven literals of `RamanujanNumerics.v2`'s `updated.c`. -/
def xs : List ℚ := [131 / 2048, 1812943298272261 / 73786976294838206464,
  3909058864302483 / 302231454903657293676544, 676174295142959 / 77371252455336267181195264,
  1 / 1099511627776, 1 / 1099511627776, 1 / 1099511627776]

theorem decode_k :
    decode PVRamanujan.V2.program = some (xs, 4096, [(.minus, 134), (.minus, 119)]) :=
  decode_of_decodeL (by decide +kernel)

theorem budget_k : budgetFrom PVRamanujan.V2.source PVRamanujan.V2.program 119 131 3914 3915
    (1 / 10 ^ 10) (9101 / 1000) xs 4096 [(.minus, 134), (.minus, 119)] = true := by
  decide +kernel

theorem certificate_k : budgetCheck PVRamanujan.V2.source PVRamanujan.V2.program 119 131 3914 3915
    (1 / 10 ^ 10) (9101 / 1000) = true :=
  budgetCheck_of_decode decode_k budget_k

/-- `RamanujanNumerics.v2.epsilon_budget`, kernel only. -/
theorem epsilon_budget : RamanujanNumerics.v2.epsilon_budget := by
  intro x hx
  have h := budget_of_check certificate_k x (by simpa using hx)
  simpa [RamanujanNumerics.v2.allowance] using h

end V2

namespace OldGrouped

def xs : List ℚ := [8902952600176047 / 9007199254740992]

theorem decode_k :
    decode PVRamanujan.OldGrouped.program = some (xs, 4096, [(.minus, 134), (.minus, 0)]) :=
  decode_of_decodeL (by decide +kernel)

theorem budget_k : budgetFrom PVRamanujan.OldGrouped.source PVRamanujan.OldGrouped.program (-1194)
    1426 3914 3915 (1 / 10 ^ 10) (39147 / 10) xs 4096 [(.minus, 134), (.minus, 0)] = true := by
  decide +kernel

theorem certificate_k : budgetCheck PVRamanujan.OldGrouped.source PVRamanujan.OldGrouped.program
    (-1194) 1426 3914 3915 (1 / 10 ^ 10) (39147 / 10) = true :=
  budgetCheck_of_decode decode_k budget_k

/-- The v1 budget from the one-entry array, kernel only. -/
theorem epsilon_budget : RamanujanNumerics.v1.epsilon_budget := by
  intro x hx
  have h := budget_of_check certificate_k x (by simpa using hx)
  have hb : (((39147 / 10 : ℚ)) : ℝ) = 3914.7 := by norm_num
  rw [hb] at h
  simpa using h

end OldGrouped

namespace UpdatedGrouped

def xs : List ℚ := [4610924128699179 / 72057594037927936]

theorem decode_k :
    decode PVRamanujan.UpdatedGrouped.program = some (xs, 4096, [(.minus, 134), (.minus, 119)]) :=
  decode_of_decodeL (by decide +kernel)

theorem budget_k : budgetFrom PVRamanujan.UpdatedGrouped.source PVRamanujan.UpdatedGrouped.program
    119 131 3914 3915 (1 / 10 ^ 10) (39147 / 10) xs 4096 [(.minus, 134), (.minus, 119)] = true := by
  decide +kernel

theorem certificate_k : budgetCheck PVRamanujan.UpdatedGrouped.source
    PVRamanujan.UpdatedGrouped.program 119 131 3914 3915 (1 / 10 ^ 10) (39147 / 10) = true :=
  budgetCheck_of_decode decode_k budget_k

/-- The updated coefficients against the threshold 3914.7, kernel only. -/
theorem epsilon_budget_fixed_target :
    ∀ x > exp 3915, DudekPlatt.v3.εUpper 131 x - DudekPlatt.v3.εLower 119 (exp 3914) x ≤ 3914.7 := by
  intro x hx
  have h := budget_of_check certificate_k x (by simpa using hx)
  have hb : (((39147 / 10 : ℚ)) : ℝ) = 3914.7 := by norm_num
  rw [hb] at h
  simpa using h

end UpdatedGrouped

end PVRamanujan.KernelOnly
