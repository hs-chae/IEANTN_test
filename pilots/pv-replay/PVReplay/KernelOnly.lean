/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVReplay.KernelChain
import PVCore.Decimal

/-!
# The A→B′ chain with no native fact

`PVPilot.Kernel` left two native facts, both decoding the decimal literals of a stage
(`decode programA`, `decode programB`). `PVCore.decode_of_decodeL` proves `decode p = some v` from
`decodeL p = some v`, and `decodeL` uses only byte-level string primitives that the kernel reduces,
so both decodings are now `decide +kernel`. Everything else is reused from `PVPilot.Kernel`
unchanged (`upperA_k`, `enclosureA_k`, `budgetB_k`, already kernel-checked), and the chain theorem
is `PVPilot.Updated.gap_of` applied to the two certificates.

`#print axioms PVPilot.KernelOnly.gap_exceeds_leading`: `propext`, `Classical.choice`,
`Quot.sound`. The remaining premise is the mathematical input `QRHCH2.v5.psi_refined_bound`.
The native-assisted routes (`PVPilot.Updated`, two certificates; `PVPilot.Kernel`, two decoding
facts) are kept: they build in seconds.
-/

namespace PVPilot.KernelOnly

open Real PVCore CalibrationPilot PVPilot.Updated PVPilot.Kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Stage A's literals, decoded by the kernel. -/
theorem decodeA : decode programA = some (xsA, 4096, [(.minus, 0), (.minus, 0)]) :=
  decode_of_decodeL (by decide +kernel)

/-- Stage B′'s literals, decoded by the kernel. -/
theorem decodeB : decode programB = some (xsB, 4096, [(.minus, 134), (.minus, 0)]) :=
  decode_of_decodeL (by decide +kernel)

theorem certificateA : CertA := by
  obtain ⟨hu, hx, hs, ho⟩ := upperCheck_of_decode decodeA upperA_k
  exact ⟨hu, ho, by rw [hs, hx]; exact enclosureA_k⟩

theorem certificateB : CertB := PVRamanujan.budgetCheck_of_decode decodeB budgetB_k

/-- **Chain theorem, kernel only.** The statement of `PVPilot.Updated.gap_exceeds_leading`. -/
theorem gap_exceeds_leading (hpsi : QRHCH2.v5.psi_refined_bound) :
    ∀ x > exp 9401,
      (1 + (68431 / 5000) / log x) * x ^ 2 / log x ^ 6 < ForwardRamanujan.gap x :=
  gap_of certificateA certificateB hpsi

end PVPilot.KernelOnly
