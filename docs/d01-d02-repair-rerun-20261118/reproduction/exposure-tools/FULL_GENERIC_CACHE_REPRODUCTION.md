# Reproduce the complete ordinary Mathlib cache

The portable companion `scripts/reproduce_full_generic_cache.py` completes the historical IEANTN generic environment after `scripts/reproduce_baselines.py`. It uses the completed recipe's own pinned compiler, original sources, core proof objects and two selected DP contexts. It never requires this research host's original checkouts, installed Lean, host generic-cache map, model account or candidate submissions.

The baseline recipe remains unchanged. The supplement copies only frozen generic source files and the baseline's generic objects into a separate owned directory, fetches the official same-pin Mathlib and Mathlib.Tactic cache, restores every previous generic row byte-for-byte, and tests the original core and selected consumers against the expanded cache. Existing baseline sources, platform files and application proof artifacts are rehashed both before and after the supplement.

## Clean-environment commands

Keep `reproduce_baselines.py`, `baseline_reproduction_pins.json.gz` and `reproduce_full_generic_cache.py` together under `scripts/`. Use Linux x86-64, Python 3 with the standard library, a working user systemd manager, `taskset`, `cp`, GNU `time`, `tar`, `zstd`, and network access to the frozen official GitHub release/source archives and official Mathlib cache service. The baseline documentation lists the exact compiler/dependency pins and prerequisites.

```sh
python3 scripts/reproduce_baselines.py \
  --out /absolute/fresh-baseline --memory-gib 32 --scratch-gib 48

python3 scripts/reproduce_full_generic_cache.py \
  --baseline /absolute/fresh-baseline \
  --out /absolute/fresh-full-generic --memory-gib 32 --scratch-gib 32
```

Both output directories must be fresh and disjoint. The supplement refuses to overwrite an existing result or place its output inside the baseline. By default the scripts select at most eight available CPUs; `--cpus 80-87` was used in the recorded host run. On a shared study host, obtain a valid shared resource reservation or wait until the study drains; do not treat an otherwise ample host as permission to exceed the participant's locked CPU/RAM allocation.

The scripts establish an actual memory cgroup, no swap, at most eight affinity CPUs and a descriptor allowance of 65,536. The supplement checks available RAM independently of disk space and guards its owned scratch allocation. All new writes, downloads, command logs, source copies and cache objects stay below the fresh supplement output. It never deletes either output tree. There are no random seeds or randomized numerical inputs in this deterministic setup.

Quick no-write pin checks, including optimization-safe execution, are:

```sh
python3 scripts/reproduce_full_generic_cache.py --validate-pins
python3 -O scripts/reproduce_full_generic_cache.py --validate-pins
python3 -OO scripts/reproduce_full_generic_cache.py --validate-pins
```

The baseline script SHA256 is `3f6715744151cfbf46354c648a3a192250acfc17addbfba92da316af366bb13e`; compressed frozen pin manifest SHA256 is `de395902e63692e37c7e043f8c2799b3ea84e3a8929aed21048ea12adf336555`. The companion checks both before accepting work. Mathlib remains `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`, Lean remains 4.34.0-rc2, and historical IEANTN remains `ef21db9ba5dceffd976da71e24f8497b3a13f798`.

## Actual recorded supplement

The completed public-archive/toolchain/bootstrap baseline is `reproduction-cold-v1`. The actual supplement consumed that output directly and wrote `reproduction-cold-full-generic-v1`; it did not use a host cache map. Its `RESULT.json` SHA256 is `48780bdc240254089babf3be690c0b3fabe2a878829585ae1a5793e22e57e460`.

| Item | Actual result |
| --- | --- |
| Supplement status | PASS_PORTABLE_SAME_OWNED_BASELINE_FULL_GENERIC_CACHE_SUPPLEMENT |
| Script active time | 68.33 seconds |
| Official same-pin full-cache command | 20.98 seconds |
| Existing generic file rows preserved | 48,246 |
| Expanded generic file rows | 115,300 |
| Restored overwrites | 12 `.trace` metadata files; downloaded versions retained separately |
| Charged RAM sampled maximum | 9,065,508,864 bytes; a lower bound on the exact simultaneous peak |
| Memory limit / swap / affinity | Actual 32 GiB / zero / CPUs 80–87 |
| Observed OOM / OOM-kill events | 0 / 0 |
| Allocated disk sampled maximum | 7,739,482,112 bytes |
| Model calls | 0 |

The successful checks imported Mathlib and Mathlib.Tactic and executed ordinary proof-producing arithmetic tactics. They imported the original core consumers and, in two separate `Solution` contexts, checked the original DPv3 criterion and DPv2 Ramanujan implication. Both selected theorem dependency lists remained exactly propext, Classical.choice and Quot.sound. The DPv2 numerical/analytic hypotheses and DPv3 criterion parameters remain explicit; the supplement supplies no new numerical fact. Core compilation does not prove every original `Challenge` interface.

`INVOCATION.json` preserves the actual command and source pin. `COMMANDS.jsonl` records exact cache/compiler arguments, working directories, stdout/stderr hashes and GNU-time receipts. `RESULT.json` binds original source commits, all command receipts, consumers and eight compressed exhaustive object manifests. `ACTUAL_RESOURCE_START.json` and `RESOURCE_END.json` preserve actual caps, affinity, memory events and sampled RAM/disk. Exact cgroup memory.peak was unavailable. The original baseline application proof artifacts and toolchain/source files passed the final unchanged-byte check.

The 12 restored files were eleven Mathlib Cache utility trace files and Batteries/Tactic/OpenPrivate.trace. No previous proof object was replaced. Their downloaded copies are retained in the supplement's owned `official-overwrites-preserved` directory. Cache/source association and successful import checks retain the existing official compiler/generic-cache trust boundary; this is not an all-source compiler/Mathlib rebuild and not source-first program verification.

## Resource-policy deviation and preservation

The actual supplement and two review-preflight attempts ran during the first main discovery block without entries in the shared participant-A reservation registry. Their CPUs 80–87 were disjoint from main CPUs 32–55, and separate host capacity was ample, but adding these configured allocations exceeded A's locked 192 GiB/24-CPU allocation. Their impact on main execution was not measured. This is an explicitly retained coordinator setup-policy deviation, not evidence of zero impact or complete protocol compliance. See `evidence/COORDINATOR_SETUP_RESOURCE_OVERLAP.json` for journal UTC intervals, actual available telemetry and missing telemetry. Original source, protocol, mathematical outcomes and failed setup evidence were not changed or relabeled.

No uninterrupted repeat of the entire baseline-plus-supplement from another fresh root was performed after this supplement. The public-source baseline previously completed across its preserved technical failures/resumes; the actual companion then completed directly against that owned cold output. This is the precise tested scope.

The large copied generic caches and fresh official cache downloads are deterministically regenerable. Keep the scripts, frozen pins, command/resource/source receipts, compressed manifests, original research sources and accepted proof evidence. Cleanup of large supplement data must wait until the final reproduction procedure and active mount dependencies are checked, and must target only the verified owned temporary tree. No cleanup has been performed by this companion.
