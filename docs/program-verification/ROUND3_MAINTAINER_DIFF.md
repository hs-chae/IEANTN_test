# Round 3: modifications outside solution-local areas

Check: `git diff --stat ce12611..qrh-2pv_B -- . ':!Solutions/QRHGlobalIntervals.v1' ':!Solutions/Table4Evolution.v1' ':!docs/program-verification' ':!pv-evidence'`.
Every change is an addition; nothing existing was modified or deleted.

| Path | Kind | Who is affected | Why it is needed | Why a smaller workaround did not do |
|---|---|---|---|---|
| `Solutions/ProgramVerification/PVCore/Decimal.lean` (new module, 199 lines) | shared verification package (a `Solutions/` project, not core) | nobody unless imported; no existing module imports it | the kernel-only route needs `decode p = some v` without native evaluation, for three programs in two projects | a per-project copy would duplicate the soundness proof three times; the module adds definitions and theorems only |
| `pilots/pv-replay/PVReplay/KernelOnly.lean` (new), `PVReplay.lean` (+1 import) | pilot | the pilot only | the kernel-only A→B′ chain lives next to the round-2 chain it reuses | — |
| `pilots/pv-replay/tests/AxiomsKernelOnly.lean` (new) | test | — | axiom audit | — |
| `scripts/native_assisted/endpoints.json` (+11 entries) | local gate registry | the local gate only | the new endpoints must be audited | — |

**Not changed:** the IEANTN core (`IEANTN/`), node metadata (`formalization.yaml`), `scripts/ieantn.py`,
the page generator, CI-owned `docs/nodes`, `STATE.md`, `GRAPH.md`, any statement, fingerprint,
`designated` value, receipt, or another contributor's solution. Agent A's code is untouched; the
Agent A configurations take its θ bound as a hypothesis.

**Inherited, unchanged.** `ieantn.py check` still fails only on the 49 inherited receipt-provenance
items (`teorth/IEANTN` against `hs-chae/IEANTN_test`), as in rounds 1 and 2.

**Node registration (proposal only, not implemented).** The two global interval theorems could be
conclusions of a new node whose imports are `QRHPropagation.v2.theta_frontier`,
`Dusart2018.v1.proposition_5_4`, `KadiriLumley.v1.table_2` and `PrimeInterval.v1.eTheta_criterion`,
with `Solutions/QRHGlobalIntervals.v1` as the solution. The statements use only core vocabulary
(`HasPrimeInInterval`, `Nat.Prime`), so no vocabulary move is needed. This is the owner's call.
