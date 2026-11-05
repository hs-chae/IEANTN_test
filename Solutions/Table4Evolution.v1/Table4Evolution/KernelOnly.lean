/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.QRHTrunc
import PVCore.Decimal

/-!
# The two-cell QRH transport with no native fact

`QRHTrunc.certificate` is one `native_decide`. Here the same facts are proved by the kernel:
decoding the literals of the actual C file (`PVCore.decode_of_decodeL`), the shared-contract check
on the decoded values (`upperFrom`: token matching, the binary64 chain, the suffix rounding), the
cell certificates (`cellsOK`, seven exponential enclosures by exact rational Taylor bounds) and the
constants (`constOK`). Then `pi_bound` gives `FKS2Numerics.v7.qrh_pi` exactly as before.

`#print axioms Table4Evolution.QRHTrunc.Kernel.qrh_pi`: `propext`, `Classical.choice`,
`Quot.sound`. The premises are the challenge's: `QRHCH2.v5.psi_refined_bound` and the anchor
`FKS2.v6.table4_anchor_300`.
-/

namespace Table4Evolution.QRHTrunc.Kernel

open Real IEANTN PVCore Table4Evolution Table4Evolution.QRHTrunc

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem decode_k : decode program =
    some (xsQ, 1 / 2 ^ 55, [(.plus, anchorQ), (.plus, pointQ), (.plus, tailQ)]) :=
  decode_of_decodeL (by decide +kernel)

theorem upper_k : upperFrom source program (1 / 10 ^ 30) (5 / 10 ^ 16) xsQ (1 / 2 ^ 55)
    [(.plus, anchorQ), (.plus, pointQ), (.plus, tailQ)] = true := by
  decide +kernel

theorem cells_k : cellsOK (1 / 8) 55 qrhM bs xsQ = true := by
  decide +kernel

theorem const_k : constOK (1 / 8) (qrhM 300) (qrhM 330) anchorQ pointQ tailQ = true := by
  decide +kernel

/-- The shared-contract certificate of the actual C file, assembled in the kernel. -/
theorem certificate_k : upperCheck source program (1 / 10 ^ 30) (5 / 10 ^ 16) = true :=
  (upperCheck_of_decode decode_k upper_k).1

/-- `FKS2Numerics.v7.qrh_pi`, kernel only. -/
theorem qrh_pi (hpsi : QRHCH2.v5.psi_refined_bound) (hAnchor : FKS2.v6.table4_anchor_300) :
    FKS2Numerics.v7.qrh_pi := by
  obtain ⟨hu, hx, hs, ho⟩ := upperCheck_of_decode decode_k upper_k
  have hb := program_bound hu hs ho
  rw [hx] at hb
  have h := pi_bound (rest := [329, 330]) (profile_qrh hpsi) hAnchor cells_k (by decide) const_k hb
  show HasNumericalBound Eπ ((5 : ℝ) / 10 ^ 16) (exp 330)
  norm_num at h ⊢
  exact h

end Table4Evolution.QRHTrunc.Kernel
