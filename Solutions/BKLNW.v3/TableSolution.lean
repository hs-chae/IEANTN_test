/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import TableReplay
import IEANTN.Nodes.BKLNW.v3.Conclusions

theorem BKLNW.v3.challenge_table8_qrh_replay
    (hpsi : QRHCH2.v2.psi_density_frontier) : BKLNW.v3.table8_qrh_replay :=
  QRHTableReplay.table_updates hpsi
