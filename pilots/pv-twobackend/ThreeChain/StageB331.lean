/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVRamanujan.Family
import PVRamanujan.Kernel
import PVCore.Kernel
import PVCore.Decimal

/-!
# Stage 3: the Ramanujan budget program at `(m, M, A, Y) = (0, 122.5, 330, 331)`, kernel only

The same family as `TwoBackend.StageB` (`scripts/native_assisted/pv_update.py`, family
`ramanujan-budget`), regenerated at `A = 330`, `Y = 331`: the power-form transport's bound starts at
`e^330`. Certified output upper value `112.1461307926`; the stated bound is `112.15`. Decoding and the
budget check are `decide +kernel` (no native fact).
-/

namespace PVThreeChain.StageB

open Real PVCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The array literals of the selected file `c/budget_331.c`. -/
def literals : List String := [
    "0.059814453125",
    "0.0002780695336102719460689980390810660537681542336940765380859375",
    "0.0000017336589320104783446571498906063624190210248343646526336669921875",
    "0.0000000137740514251176168653070447443591273195551138996961526572704315185546875",
    "0.000000000119592901601077912033751153209515556696818094906120677478611469268798828125",
    "0.00000000000092208776725403102459950804644999320324426361761283033047220669686794281005859375",
    "0.0000000000009094947017729282379150390625"]

def program : Program := PVRamanujan.program literals "4096.0" "134.0" "0.0"

/-- The selected C file. The lakefile declares it as an `input_file` this library `needs`. -/
def source : String := include_str ".." / "c" / "budget_331.c"

/-- The literals' exact binary64 values. -/
def xs : List ℚ := [245 / 4096, 5129477521204463 / 18446744073709551616,
  2046743208313467 / 1180591620717411303424, 8325903204262183 / 604462909807314587353088,
  2313263145410797 / 19342813113834066795298816, 4565957467276095 / 4951760157141521099596496896,
  1 / 1099511627776]

theorem decode_k : decode program = some (xs, 4096, [(.minus, 134), (.minus, 0)]) :=
  decode_of_decodeL (by decide +kernel)

theorem budget_k : PVRamanujan.budgetFrom source program 0 (245 / 2) 330 331 (1 / 10000000000)
    (11215 / 100) xs 4096 [(.minus, 134), (.minus, 0)] = true := by
  decide +kernel

/-- The stage's certificate, assembled in the kernel. -/
theorem certificate_k : PVRamanujan.budgetCheck source program 0 (245 / 2) 330 331 (1 / 10000000000)
    (11215 / 100) = true :=
  PVRamanujan.budgetCheck_of_decode decode_k budget_k

/-- Stage 3's input contract at exactly the certified parameters. -/
theorem budget : ∀ x > exp (331 : ℝ), DudekPlatt.v3.εUpper (245 / 2) x -
    DudekPlatt.v3.εLower 0 (exp 330) x ≤ 11215 / 100 := by
  intro x hx
  have h := PVRamanujan.budget_of_check certificate_k x (by exact_mod_cast hx)
  norm_num at h
  linarith

end PVThreeChain.StageB
