# Owner decisions

Four decisions, each against doing nothing. None changes IEANTN's architecture, schema, Vocabulary, node kinds,
justification kinds, receipts or trust levels. Items 2 and 3 edit the owner's PoC branch and need the owner's
approval; nothing here has been applied outside disposable worktrees.

## 1. Proof routes are justifications, never node versions (documentation)

| | |
|---|---|
| Do nothing | A new route of an existing statement keeps landing as a new version, as `FKS2Numerics.v7` did (`154b1d0`): one duplicate statement plus two in consumers. M1's layout B reproduced the pattern at once: its provider became a third copy of the same statement |
| Minimal option | One paragraph in NODES.md near L206 ("several justifications"): a new proof of an existing statement is a justification (designated or spare); a Lean route that lives in another solution project is attached through a thin `Solutions/<NodeId>/Solution.lean` that requires that project by path (measured in M1–M3: 1-line proofs) |
| Measured benefit | prevents the only architectural duplicate class found (casebook C5); the local registry already holds 5 routes for `FKS2Numerics.v7.qrh_pi` and 5 for `RamanujanNumerics.v1.epsilon_budget` without new nodes |
| Concrete cost | about 10 lines of documentation; no code |
| Recommendation | **adopt**, together with the promotion rule N1–N3 as review guidance, not CI (rule stress test §4) |

## 2. Re-designate the paper proof of `RosserSchoenfeld.v1.zero_free_region` on the PoC (one YAML line)

| | |
|---|---|
| Do nothing | On the PoC the unconditional zero-free region and three conclusions bridged from it rest on QRH in the dependency report. Upstream's `diff` rejects the branch with four "gained unproved assumptions" errors, and that error has no acknowledgement override |
| Minimal option | `designated: rs-paper` (the paper justification is still listed); keep the QRH bridge as a spare |
| Measured benefit | upstream's `diff --base ef21db9` then reports 0 breaking changes; the four leaf sets return to their base values (`evidence/leafset/L4`, `L5`) |
| Concrete cost | one line; no Lean |
| Recommendation | **adopt** before anything from the PoC is proposed upstream. It is the owner's branch, so the owner decides |

## 3. Declare every `include_str` source to Lake on the PoC (configuration)

| | |
|---|---|
| Do nothing | 7 of the 12 PoC projects that read C files through `include_str` declare none of them (20 files, including the designated providers `FKS2Numerics.v6` and `RamanujanNumerics.v1`, and the A→B′ pilots). Editing one literal of program B′ rebuilt nothing and the build succeeded in both layouts: a stale certificate (MT10b). The local gate's source check would catch it at the next attestation; Lake, `status` and receipts do not |
| Minimal option | add `[[input_file]]` entries with `needs` on the reading library, as `Table4Evolution.v1`, `RamanujanNumerics.v2/v3`, `FKS2Numerics.v5` and `pv-twobackend` already do (about 5 TOML lines per file) |
| Measured benefit | tested on the A→B′ pilot: with its two C files declared (15 TOML lines) the MT10b literal edit makes the build fail in `PVReplay.Chain`, where without the declaration the build succeeded on the old embedded source (`PV_NODE_SPLIT_MUTATION_TESTS.md`, R2) |
| Concrete cost | about 100 lines of TOML in 7 lakefiles; every build reading those files re-traces once. One of the seven, `Solutions/RamanujanNumerics.v1`, is under the forward-experiment freeze manifest (its files are SHA-pinned), so its lakefile edit needs the owner's explicit exception or must wait |
| Recommendation | **adopt on the PoC.** Upstream has no `include_str` user, so nothing to do there yet |

## 4. Make `solution_drift` see files in the solution projects a solution requires (tooling, optional)

| | |
|---|---|
| Do nothing | A receipt for a solution that reads a program from another project stays green after that program is edited; the owning project's drift line calls the edit "no Lean source among them", the wording meant for a manifest bump. Today only the PoC has such solutions, and its local gate pins C hashes per endpoint |
| Minimal option | the 32-line patch on upstream `466b41b` (`evidence/remedy/0001-*.patch`): diff the in-repository path dependencies listed in the solution's committed `lake-manifest.json`, leaving out the core; name non-Lean sources in the drift line |
| Measured benefit | reported the edit from the node's own project in every cross-project mutation, where the current tool reported nothing (mutation tests); 5 new tests fail before and pass after; upstream's 357 tests pass |
| Concrete cost | 32 lines in `scripts/ieantn.py`, 75 lines of tests; no schema or receipt change; one extra `git diff` path list per receipt. Package-level, so occasionally noisy: it flagged `RamanujanGap.v3` for an edit outside that solution's import closure (MT11) |
| Recommendation | **do nothing now**; propose it upstream together with the first program-verified solution that reads files from another project |

## Not proposed

A new node kind, justification kind, trust level, receipt field, Vocabulary definition, evidence graph or
per-program-stage nodes: the matched experiments show no trust or cost benefit that the existing mechanisms do
not already give (extended study §4–7). Agent A's winner should stay at the solution level until its source
facts are registered as nodes (casebook C3).
