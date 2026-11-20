# Exact same-input Check0006 proof-decomposition pilot

The original fixed 90,670,946-record high-count proposal is unchanged. This pilot checks precisely the original 32,768 records starting at196608, as eight disjoint4,096-record facts, then composes the exact original full Boolean statement. Every numerical fact and both generic Boolean composition lemmas have empty axiom sets. No original monolithic theorem is imported or reused. This is a Lean proof-engineering result, not source-first PV or a changed numerical algorithm.

Use the pinned compiler/Mathlib and clean-library context described in BASELINE_REPRODUCTION.md. That document regenerates the entire original proposal and the necessary original Data dependency closure; its first-check-only clean route may be reused as preparation. After a clean preparation, keep its accepted Data/Gaps/raw objects or rebuild them as part of the fresh replay below. Do not substitute a new proposal or candidate. All3464 original source hashes and the packed input hash must match HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json.

The source/ directory is the complete10-module supplemental proof source: Bridge, eight checks and Final. No prime list, certificate or numerical output is hidden in these short modules. Copy it to a new experiment-owned source root. A fresh proof replay can use the existing scripts/reproduce_guarded_coupled_closure.py with that source root plus the regenerated original proposal source root, root RamanujanPV.HighCheck0006SplitPilot.Final, theorem RamanujanPV.HighCheck0006SplitPilot.part_0006_split, jobs2, memory96GiB, aggregate192GiB, two available CPUs, host reserve512GiB. Supply the memory-profile JSON below: raw data pages9GiB, original Gaps24GiB, original aggregate Data128GiB, other generic modules48GiB, split checks/Final/selected audit96GiB. The source profile and clean closure controller are already part of the main repository. Fresh output paths must not exist and must be inside the chosen context's owned scratch tree.

```json
{"exact":{"RamanujanPV.HighTransitionCount.Gaps":24,"RamanujanPV.HighTransitionCount.Data":128,"RamanujanPV.SelectedReplayAudit":96,"RamanujanPV.HighCheck0006SplitPilot.Bridge":48},"prefix":{"RamanujanPV.HighTransitionCount.Data":9,"RamanujanPV.HighCheck0006SplitPilot":96}}
```

Example after deterministic original-proposal generation:

```sh
python3 scripts/reproduce_guarded_coupled_closure.py \
  --context /absolute/CLEAN_CONTEXT.json --out /absolute/FRESH_REPLAY \
  --application-source-root /absolute/original-proposal/source \
  --application-source-root /absolute/supplemental/source \
  --root RamanujanPV.HighCheck0006SplitPilot.Final \
  --theorem RamanujanPV.HighCheck0006SplitPilot.part_0006_split \
  --profile-json /absolute/PROFILES.json --memory-gib 48 \
  --jobs 2 --aggregate-gib 192 --cpus 16,18 --host-reserve-gib 512
```

Every environment must separately satisfy the genuine RAM and disk guards. Read the fresh final receipt with that controller's --check under normal Python, -O and -OO. This complete cold high-data-plus-pilot replay is a procedure, not an already performed clean-machine run. The recorded actual pilot used the locked, already compiled original Data objects and fresh supplemental modules. Its10 accepted compiler receipts and all parameter/source/object hashes are included here.

Actual eight-check phase:70.372s; accepted final composition4.229s; worker CPU125.17s plus final CPU in RESULT.json. The74.600s sum of separate phases is not one continuous recorded run. Actual first-worker-to-accepted-final wall time131.049s includes a failed48GiB final import and manual96GiB retry. The original same32,768-record check took5501.841s; CPU scheduling, concurrency and proof granularity differ, so this single pilot does not establish a general performance distribution.

One final48GiB import failed despite the original object existing unchanged; the identical Final succeeds at96GiB. No OS OOM kill was observed. All preparatory failures remain preserved. Complete GNU-time per-process peak RSS/CPU are retained. The V1 orchestration failed before saving its in-memory aggregate-RSS trace, so no actual aggregate-RAM peak is claimed. Existing source/Data/old Check0006 object hashes match before and after.

The source/ files, locked original proposal generator and pinned dependencies are sufficient for deterministic regeneration. No random seed is used. The pilot created only small proof modules/logs; it created no additional large data set. Existing original sources and accepted proof objects were not deleted. The full prime-count theorem and global finite Ramanujan range remain outside this result.
