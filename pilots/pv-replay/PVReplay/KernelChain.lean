/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVReplay.Chain
import PVCore.Kernel
import PVRamanujan.Kernel

/-!
# KernelB: the A→B′ chain with two native facts, both literal decoding

`PVPilot.Updated` proves the chain from two certificates, each one `native_decide` over the whole
shared check. Here the same two certificates are proved by the kernel route of
`PVCore.Kernel`: for each stage, **one native fact decodes the decimal literals** of the program
(`PVCore.decode`), and the kernel (`decide +kernel`) checks everything else on the decoded
rationals: token matching of the actual source, the binary64 summation chain, the suffix rounding,
the enclosure and the final budget. The chain theorem is then `PVPilot.Updated.gap_of` applied to
these certificates: same statement, same two stages, and the native trusted computation is
parsing only.

This is the trust-reduction recipe of `CalibrationPilot.KernelA` (prompt 1), now generic in the
shared contract and applied to both stages (prompt 1 called the B′ half "KernelB").
-/

namespace PVPilot.Kernel

open Real PVCore CalibrationPilot PVPilot.Updated

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Stage A's literals, decoded: exact binary64 values. -/
def xsA : List ℚ := [(1/1099511627776), (7378697629483821/151115727451828646838272), (1/1099511627776), (5519305075245545/295147905179352825856), (1/1099511627776), (8417527399863843/2361183241434822606848), (1/1099511627776)]

/-- Stage B′'s literals, decoded. -/
def xsB : List ℚ := [(8450681004537519/144115188075855872), (713184690732351/73786976294838206464), (5132033806430041/2417851639229258349412352), (1/1099511627776), (1/1099511627776), (1/1099511627776), (1/1099511627776)]

/-- **Native fact 1 of 2**: decoding stage A's literals. -/
theorem decodeA : decode programA = some (xsA, 4096, [(.minus, 0), (.minus, 0)]) := by
  native_decide

/-- **Native fact 2 of 2**: decoding stage B′'s literals. -/
theorem decodeB : decode programB = some (xsB, 4096, [(.minus, 134), (.minus, 0)]) := by
  native_decide

/-- Stage A's check on the decoded literals, by the kernel. -/
theorem upperA_k :
    upperFrom sourceA programA (1 / 10 ^ 10) NewA.bound xsA 4096 [(.minus, 0), (.minus, 0)] =
      true := by
  decide +kernel

/-- Stage A's enclosure of the calibration targets, by the kernel. -/
theorem enclosureA_k : NewA.targets.sum ≤ 4096 * xsA.sum := by
  decide +kernel

/-- Stage B′'s check on the decoded literals, by the kernel. -/
theorem budgetB_k :
    PVRamanujan.budgetFrom sourceB programB NewB.m NewB.M NewB.A NewB.Y (1 / 10 ^ 10) NewB.bound
      xsB 4096 [(.minus, 134), (.minus, 0)] = true := by
  decide +kernel

theorem certificateA : CertA := by
  obtain ⟨hu, hx, hs, ho⟩ := upperCheck_of_decode decodeA upperA_k
  exact ⟨hu, ho, by rw [hs, hx]; exact enclosureA_k⟩

theorem certificateB : CertB := PVRamanujan.budgetCheck_of_decode decodeB budgetB_k

/-- **Chain theorem, kernel route.** The statement of `PVPilot.Updated.gap_exceeds_leading`. -/
theorem gap_exceeds_leading (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ x > exp 9401,
      (1 + (68431 / 5000) / log x) * x ^ 2 / log x ^ 6 < ForwardRamanujan.gap x :=
  gap_of certificateA certificateB hpsi

end PVPilot.Kernel
