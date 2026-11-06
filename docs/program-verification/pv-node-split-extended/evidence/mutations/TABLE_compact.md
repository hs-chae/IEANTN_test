| Mutation (file) | Layout | Build after the edit: project rc / modules rebuilt | Restore | Fingerprints | In-memory receipt | `solution_drift`, node's project: current / patched |
|---|---|---|---|---|---|---|
| MT1 `qrh_trunc2.c` | A | A: ok / 8 | ok / 8, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT1 `qrh_trunc2.c` | B | P: ok / 8; C: ok / 0 | ok / 8; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / none |
| MT2 `qrh_trunc2.c` | A | A: FAIL / 5 (fails in `Table4Evolution.QRHTrunc`) | ok / 6, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT2 `qrh_trunc2.c` | B | P: FAIL / 5 (fails in `Table4Evolution.QRHTrunc`); C: ok / 0 | ok / 6; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / none |
| MT3 `qrh_trunc2.c` | A | A: FAIL / 5 (fails in `Table4Evolution.QRHTrunc`) | ok / 6, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT3 `qrh_trunc2.c` | B | P: FAIL / 5 (fails in `Table4Evolution.QRHTrunc`); C: ok / 0 | ok / 6; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / none |
| MT8 `Profiles.lean` | A | A: ok / 1 | ok / 1, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT8 `Profiles.lean` | B | P: ok / 1; C: ok / 0 | ok / 1; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / none |
| MT10 `ramanujan_9401_new.c` | A | A: ok / 0 | ok / 0, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT10 `ramanujan_9401_new.c` | B | P: ok / 0; C: ok / 0 | ok / 0; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / reported |
| MT10b `ramanujan_9401_new.c` | A | A: ok / 0 | ok / 0, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT10b `ramanujan_9401_new.c` | B | P: ok / 0; C: ok / 0 | ok / 0; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / reported |
| MT9 `NewA.lean` | A | A: FAIL / 1 (fails in `CalibrationPilot.NewChain`) | ok / 2, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT9 `NewA.lean` | B | P: FAIL / 1 (fails in `CalibrationPilot.NewChain`); C: FAIL / 0 (fails in `CalibrationPilot.NewChain`) | ok / 2; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / reported |
| MT11 `Applications.lean` | A | A1: ok / 1; A2: ok / 0 | ok / 1; ok / 0, bytes identical, tree clean | n/a | n/a | A1: none / reported; A2: none / reported |
| MT11 `Applications.lean` | B | P: ok / 1; C: ok / 0 | ok / 1; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / reported |
| MT6 `Solution.lean` | A | A: ok / 1 | ok / 1, bytes identical, tree clean | n/a | n/a | A: reported / reported |
| MT6 `Solution.lean` | B | P: ok / 1; C: ok / 0 | ok / 1; ok / 0, bytes identical, tree clean | n/a | n/a | P: reported / reported; C: none / none |
| MT4 `Conclusions.lean` | A | A: FAIL / 0 (fails in `RefinedConsumer`) | ok / 1, bytes identical, tree clean | moved: `QRHCH2.v5.psi_refined_bound` | A: BROKEN | A: none / none |
| MT4 `Conclusions.lean` | B | P: FAIL / 0 (fails in `RefinedConsumer`); C: ok / 0 | ok / 1; ok / 0, bytes identical, tree clean | moved: `QRHCH2.v5.psi_refined_bound` | P: BROKEN; C: green | P: none / none; C: none / none |
| MT5 `Conclusions.lean` | A | A: FAIL / 0 (fails in `Solution`) | ok / 1, bytes identical, tree clean | moved: `PVMatchT4A.v1.qrh_absolute_pi` | A: BROKEN | A: none / none |
| MT5 `Conclusions.lean` | B | P: FAIL / 0 (fails in `Solution`); C: FAIL / 0 (fails in `Solution`) | ok / 1; ok / 1, bytes identical, tree clean | moved: `PVMatchT4P.v1.qrh_pi` | P: BROKEN; C: BROKEN | P: none / none; C: none / none |
