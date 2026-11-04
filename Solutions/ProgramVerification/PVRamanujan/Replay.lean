/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVRamanujan.Family
import ForwardRamanujan.Old
import ForwardRamanujanUpdate.Updated
import ForwardRamanujanUpdate.OldGrouped
import ForwardRamanujanUpdate.UpdatedGrouped
import IEANTN.Nodes.RamanujanNumerics.v1.Conclusions
import IEANTN.Nodes.RamanujanNumerics.v2.Conclusions

/-!
# The four existing Ramanujan-budget instances, re-derived on the shared contract

Each instance below is its selected file (unchanged, read in place), its literals (the existing
definitions, not copies), its parameters, one certificate and one short theorem. The statements
proved are the node conclusions `RamanujanNumerics.v1.epsilon_budget` and
`RamanujanNumerics.v2.epsilon_budget`, plus the grouped variants. The designated proofs of those
nodes are untouched; these are second routes that show the shared contract carries them.

The instances have 7 array entries (`V1`, `V2`) or 1 (`OldGrouped`, `UpdatedGrouped`): the same
contract handles both lengths.
-/

namespace PVRamanujan

open Real PVCore

namespace V1

def program : Program := PVRamanujan.program ForwardRamanujan.Old.literals "4096.0" "134.0" "0.0"
def source : String := include_str ".." / ".." / "RamanujanNumerics.v1" / "c" / "baseline.c"

theorem certificate :
    budgetCheck source program (-1194) 1426 3914 3915 (1 / 10 ^ 10) (39147 / 10) = true := by
  native_decide

/-- `RamanujanNumerics.v1.epsilon_budget` through the shared contract. -/
theorem epsilon_budget : RamanujanNumerics.v1.epsilon_budget := by
  intro x hx
  have h := budget_of_check certificate x (by simpa using hx)
  have hb : (((39147 / 10 : ℚ)) : ℝ) = 3914.7 := by norm_num
  rw [hb] at h
  simpa using h

end V1

namespace V2

def program : Program :=
  PVRamanujan.program ForwardRamanujan.Updated.literals "4096.0" "134.0" "119.0"
def source : String := include_str ".." / ".." / "RamanujanNumerics.v2" / "c" / "updated.c"

theorem certificate :
    budgetCheck source program 119 131 3914 3915 (1 / 10 ^ 10) (9101 / 1000) = true := by
  native_decide

/-- `RamanujanNumerics.v2.epsilon_budget` through the shared contract. -/
theorem epsilon_budget : RamanujanNumerics.v2.epsilon_budget := by
  intro x hx
  have h := budget_of_check certificate x (by simpa using hx)
  simpa [RamanujanNumerics.v2.allowance] using h

end V2

namespace OldGrouped

def program : Program :=
  PVRamanujan.program ForwardRamanujan.OldGrouped.literals "4096.0" "134.0" "0.0"
def source : String := include_str ".." / ".." / "RamanujanNumerics.v2" / "c" / "oldgrouped.c"

theorem certificate :
    budgetCheck source program (-1194) 1426 3914 3915 (1 / 10 ^ 10) (39147 / 10) = true := by
  native_decide

/-- The v1 budget again, from a one-entry array. -/
theorem epsilon_budget : RamanujanNumerics.v1.epsilon_budget := by
  intro x hx
  have h := budget_of_check certificate x (by simpa using hx)
  have hb : (((39147 / 10 : ℚ)) : ℝ) = 3914.7 := by norm_num
  rw [hb] at h
  simpa using h

end OldGrouped

namespace UpdatedGrouped

def program : Program :=
  PVRamanujan.program ForwardRamanujan.UpdatedGrouped.literals "4096.0" "134.0" "119.0"
def source : String := include_str ".." / ".." / "RamanujanNumerics.v2" / "c" / "updatedgrouped.c"

theorem certificate :
    budgetCheck source program 119 131 3914 3915 (1 / 10 ^ 10) (39147 / 10) = true := by
  native_decide

/-- The updated coefficients against the old threshold 3914.7, from a one-entry array. -/
theorem epsilon_budget_fixed_target :
    ∀ x > exp 3915, DudekPlatt.v3.εUpper 131 x - DudekPlatt.v3.εLower 119 (exp 3914) x ≤ 3914.7 := by
  intro x hx
  have h := budget_of_check certificate x (by simpa using hx)
  have hb : (((39147 / 10 : ℚ)) : ℝ) = 3914.7 := by norm_num
  rw [hb] at h
  simpa using h

end UpdatedGrouped

end PVRamanujan
