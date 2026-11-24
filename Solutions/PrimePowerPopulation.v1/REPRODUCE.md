# Reproduce the power-population solution

This is a normal Lean-kernel proof build. It does not perform source-first
C/C++/CUDA program verification. Five headline theorems consume exactly the
existing `PrimeInterval.v4.optimized_strict_family`; the sixth theorem is an
elementary strict comparison and has no analytic input.

Start at a clean checkout of the campaign branch
`research/rh-one-prime-network-20261124`. The frozen predecessor is
`3539bbba83db8345db1c43f37a9ddb6d8baf3ab0`. Use Lean 4.34.0-rc2 and Mathlib
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. The campaign's final publication
record supplies the exact new commit. Original predecessor outcomes are unchanged.

From the repository root, with pinned generic Lean/Mathlib packages available:

```bash
python3 Solutions/RHOnePrimeEvolution.v1/scripts/rebuild_closure.py \
  --repository . \
  --run /data/ieantn-power-population-clean-replay \
  --include-core \
  --source-dir Solutions/RHOnePrimeEvolution.v1/powers \
  --module-file PowerPopulationSolution=Solutions/PrimePowerPopulation.v1/Solution.lean \
  --roots PowerPopulationSolution \
  --jobs 4
```

Choose a fresh run directory. The script reads the pinned predecessor manifest of739 available source
providers, follows only the actual imports, copies and hashes the selected source
closure, and compiles every required application module. It puts no predecessor
application object directory on `LEAN_PATH`. Only pinned generic packages are
reused. `LOCAL_CONTEXT.json` records this host's generic-package paths. On a new
machine pass `--compiler /absolute/path/to/lean` and `--generic-lean-path` with the
colon-separated pinned package-library paths; inspect the generated PLAN before
claiming an identical environment. The path override does not prove that a changed
generic package is the pinned dependency.

The bounded runner permits one to four workers, two Lean threads each and64GiB
address space per compiler, and reserves host memory. It records per-module GNU
wall/user/system time and peak child RAM, sampled process-tree RAM, source and
object hashes, log hashes, allocated scratch bytes and observed SIGKILL events.
A SIGKILL count is not automatically an OOM attribution; inspect the actual logs.
The memory policy is for this authorized high-resource campaign, not a4GiB cap.

A completed compilation run writes `EXECUTION.json` with
`PASS_FRESH_TRANSITIVE_COMPILATION` and equal required/compiled module counts.
The final solution's compiler stdout prints all six actual theorem axiom lists.
These must be subsets of `propext`, `Classical.choice`, and `Quot.sound`, without
`sorryAx` or a native execution axiom. Exact-type and proof-value checks are
separate gates: `Audit.lean` checks that every canonical theorem really consumes
its expected mathematical provider and that every proof parameter is used.
The campaign's combined audit runs this check with its actual compiler-module
registration. Do not mistake the compilation status alone for that separate audit
or for a source/claim review.

The mathematical modules cover the full cube and higher-power domains; no finite
prime table, numerical seed or native execution leaf is needed. The natural
threshold uses a kernel proof of `exp(8) < 2981`. The original7301-row octic moment
certificate remains an inherited, kernel-checked input to the source-facing
family provider; the consumer does not relabel it as source-first PV.

The ordinary Lake project and Comparator configuration are supplied, but a plain
standalone `lake build` is not asserted successful: historical research proof
modules are registered by the explicit source-closure runner above. Official
Comparator dispatch and workflow receipts remain pending. No manually written
workflow receipt or `lean-comparator` status is supplied.

Keep source, exact parameters, accepted proof artifacts, concise receipts and
artifact hashes. Generated source copies, object caches and scratch may be removed
only after the final campaign verification and regeneration procedures have been
checked, within the experiment-owned run directory. Never remove the original
frozen sources or the only accepted evidence copy.
