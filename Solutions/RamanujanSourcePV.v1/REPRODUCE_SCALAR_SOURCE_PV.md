# Reproduce the selected million-window scalar source proofs

The accepted source-linked result is
`RamanujanPV.FiniteGuardedResult.source_linked_uniform_gap`: for every real x in
38,358,837,683 ≤ x < 38,359,837,684, the actual prime-count gap

e·x·π(x/e)/log(x) − π(x)²

is strictly greater than 501,901. Its proof includes the actual C counter,
segment checker, exponential, logarithm and seven-field strict checker paths.
The six source-byte/AST correspondences are retained in the result bundle.
The complete dependency audit visits 976,054 constants, requires 28 source
paths, excludes 18 old providers, and excludes every `cell_domain_*` leaf.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.

The separate generic `FiniteCellGeneric` theorem now also proves the complete
unchanged C checker under its explicit non-strict domain using the generic
source-proved logarithm. Every service response is realized by an actual
source body; totality of the older bounded128-fuel registry is not assumed.
The separate full workload is now also accepted: all1,755,663 original rows
have actual e/log/cell source executions and the additional kernel-checked
integer margin9005. `FullSourceResult.all_scalar_programs` retains all four
actual count/e/log/cell source bindings with that scalar certificate. This
does **not** establish any missing full-range prime-count output. Its global
real-gap consumer still requires every such source-count execution plus the
same24 analytic inputs. No unconditional full1.49-trillion result is claimed.

## Clean prerequisite and complete overlay

First bootstrap the pinned Lean4.34.0-rc2 compiler and generic dependencies,
as described in the project README. Create a fresh application context and
complete the local count/consumer stage:

```bash
bash scripts/reproduce_local_million_full.sh CLEAN_CONTEXT FRESH_LOCAL CPUS JOBS
```

Use the **cloned context** created by that stage for the scalar overlay. It
points to the fresh `FRESH_LOCAL/build/lean` application object directory;
the original generic-only `CLEAN_CONTEXT` points elsewhere. Paths below must
be absolute, and `FRESH_SCALAR` must be a fresh directory inside the cloned
context's owned scratch parent.

```bash
bash scripts/reproduce_finite_scalar_source_v2.sh \
  FRESH_LOCAL/network/Solutions/RamanujanSourcePV.v1/BUILD_CONTEXT.json \
  FRESH_LOCAL/proposals/million-cells/source/RamanujanPV/LocalCellsMillion/Data.lean \
  FRESH_SCALAR CPU
```

The additive V2 wrapper rebuilds all 43 ordered static scalar/consumer/audit
modules, regenerates all original 285 log, cell-execution and alternate
non-strict-domain records, compiles their 30 proof modules, runs the independent
exact-type/axiom/source-receipt validators, observes the unchanged actual C
program, and compiles the strongest guarded result and complete dependency
audits. The old V1 wrapper remains preserved as historical evidence.

The original row-source SHA-256 is
`054ad58fe66e6b22ef91c06e19c1492fd24c7636c0fc241cba7c3fe760b5294e`.
The algorithm remains F=2⁶⁰, 20 terms, denominator41, output scale2⁴⁰, with
all seven original row fields. These stages use no random seed. Proposal
generators supply untrusted inputs, and native observations are not numerical
axioms or substitutes for source execution proofs.

The separate resource knobs, in GiB, default to:

```bash
SCALAR_SOURCE_MEMORY_GIB=96
SCALAR_NUMERIC_MEMORY_GIB=24
SCALAR_FINAL_MEMORY_GIB=48
SCALAR_AUDIT_MEMORY_GIB=96
```

Each request is bounded by 300GiB and actual available RAM. Requests above
48GiB require at least1TiB genuinely available; the launcher retains512GiB
for the host. Disk is an independent allowance. No arbitrary4GiB ceiling is
used.

A safe preflight performs no compilation and creates no output directory:

```bash
bash scripts/reproduce_finite_scalar_source_v2.sh --check-prerequisites \
  FRESH_LOCAL/network/Solutions/RamanujanSourcePV.v1/BUILD_CONTEXT.json \
  FRESH_LOCAL/proposals/million-cells/source/RamanujanPV/LocalCellsMillion/Data.lean \
  FRESH_SCALAR CPU
```

Its success status is explicitly `PREREQUISITES_ONLY_NOT_REPLAYED`.

## Evidence and limits of the current reproduction checks

`evidence/scalar-source-pv-v1/PACKET.json` retains all original285 source runs,
exact source snapshots, source/object/compiler hashes, resource/axiom receipts,
independent validators and generic log proofs. That packet is immutable.
`evidence/scalar-generic-cell-and-repro-v1/PACKET.json` adds the accepted generic
cell proof and the current V2 prerequisite controls. Its 12 actual routes cover
valid preflight and rejected bad-row/outside-owned-output/over-limit cases under
normal Python, `-O`, and `-OO`. They establish preflight behavior, not a complete
new proof replay. The numerical validators and relocated deterministic
source generators have their own actual all-mode controls in the first packet.

**The complete V2 clean scalar overlay has not yet been executed.** Its accepted
constituent scientific proofs, independent audits and deterministic relocation
checks are distinct from that pending end-to-end reproduction. Likewise,
source generation or an active cold-count replay is not a completed replay.
Use each final `RESULT.json` to establish actual completion.

Compiler/runtime, unsigned128 ABI, operating-system and hardware contracts
remain explicit external boundaries. The adaptive C++ generator/caller and
physical compiled-process association are not silently assumed proved. Cleanup
must preserve original inputs, accepted Lean proofs and essential receipts;
only checked regenerable experiment-owned scratch can be removed.

## Full-workload dependency inspection

The completed `FullSourceDependencyAudit` attempt3 inspects the actual complete
proof AND type closures separately: 68,079 constants for `all_scalar_programs`
and 94,943 for `all_real_gap9005_if_counts_completed`. All33 common source,
callee, initialization, loop and row-provider paths occur; the conditional
root additionally contains all16 required count-correctness/analytic paths.
Both exclude20 old named shortcuts and every constant in11 prior local-result
namespaces. Every encountered axiom is checked against the standard three.
The conditional signature still explicitly requires `RemainingCountExecutions`
and the unchanged24 analytic hypotheses. Its generic `complete_from_counts`
consumer is required rather than forbidden.

The executed inspection took33.04seconds and peaked at10,212,667,392bytes RSS
under a96GiB ceiling. Its source, exact compiler receipts, path witnesses,
object hashes and resource/axiom output are preserved in
`evidence/full-source-dependency-audit-v1/RESULT.json`. This is an inspection of
two specified proof closures, not a full external-source or network census.
The full scalar workload's additional9005 margin is an exact integer kernel
certificate; the unchanged seven-field C checker computes its original strict
predicate. No separate C margin program or completed full count workload is
claimed.
