# Clean-environment reproduction

The current source-identical continuation uses the process-only page policy
in [PROCESS_RESOURCE_PROFILE.md](PROCESS_RESOURCE_PROFILE.md). Apply that
wrapper outside the whole coordinator/supervisor before compiler version or
context checks, including a real bootstrap fetch. The exact source and
mathematical checker remain unchanged; the physical 300GiB/no-swap and separate
RAM/disk/scratch admission still apply. Put new dependency caches and run
outputs under one owned campaign root and let the outer supervisor count
them together. A pre-exec policy receipt is neither child success nor proof
acceptance. The detailed recipe records actual CPU affinity and preserves
all prior failed/stalled resource profiles.

This entry point plans or runs the public proof and numerical pipelines. It does
not reuse historical stopped/censored experiment banks, a private research
executor, a model SDK, or a prior application object cache. Only the eight pinned
generic Lean libraries may begin as compiled objects.

**The new driver has not executed a complete heavy clean rerun.** Original exact
pipeline receipts remain evidence of their own executions. A driver plan,
format export, or successful compiler overlay is not a new complete campaign
result. Missing final W4/canonical interfaces stop the driver with an explicit
incomplete receipt. The three collaborator documents in reports/ retain their
own final-status placeholders; this driver does not rewrite them.

## Prerequisites and pinned generic context

Use Linux, Python 3.10 or newer, Git, GNU time/coreutils, and prlimit.
Install the exact Lean release leanprover/lean4:v4.34.0-rc2 in an isolated or
existing toolchain location. The retained Linux executable SHA256 is:

~~~
e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
~~~

This is a binary identity, not a compiler verification claim. Generic
compiler/runtime/API/hardware contracts remain the stated trust boundary.

Validate existing generic roots:

~~~bash
python3 Solutions/RH080Next.v1/reproduction/bootstrap_context.py \
  --from-context /path/to/existing/generic-only-context.json \
  --output /fresh/output/context.json
~~~

Or obtain generic dependencies and official caches from the exact pinned
Mathlib manifest in a **fresh workspace outside the mathematical checkout**:

~~~bash
python3 Solutions/RH080Next.v1/reproduction/bootstrap_context.py \
  --fetch --workspace /fresh/dependencies \
  --output /fresh/output/context.json
~~~

The toolchain must already exist. Supply --compiler /exact/toolchain/bin/lean
when automatic lookup is unsuitable. Bootstrap never silently replaces a
toolchain, updates shared Lake state in the mathematical checkout, or imports
application proof objects. It checks all eight revisions and clean tracked
generic sources after obtaining caches. Context and bootstrap receipts record
actual paths, hashes and commands. Different paths give different receipts;
old producer receipts are not relabelled.

| Generic package | Exact revision |
| --- | --- |
| mathlib | 71a80585ee495fc24472fd0eaffc89d94e4fd8d6 |
| plausible | d9598f07b1bc701f1e3aae163d2681c1fd978793 |
| LeanSearchClient | ba67e212be1197b84c1f1f6299488a10a3002713 |
| importGraph | 1681d78dd6e65e38b143f9740d829c826673807c |
| proofwidgets | a8acbfd87375ff4abe14ce09db5b7664d383bc7f |
| aesop | 18889deb9e83ea7420ef51c160d6f88552e744e3 |
| Qq | 507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3 |
| batteries | 4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb |

The retained physical C validator additionally requires GCC binary SHA256
821af3c74506283c179ca413bb33e6b528805a4dd8a5c09df125e5ad560a9e89,
version x86_64-linux-gnu-gcc-11 (Ubuntu 11.4.0-1ubuntu1~22.04.3) 11.4.0.
Select it with --cc. The plan checks this before starting long work; it does not
install host packages or widen access. Other compiler observations cannot be
presented as this pinned24-case receipt population.

## Inspect the concrete plan

From the repository root:

~~~bash
python3 Solutions/RH080Next.v1/reproduction/reproduce_all.py \
  --context /fresh/output/context.json --run /fresh/output/plan
~~~

The default reports PLAN_ONLY_NOT_REPRODUCED with all stages and missing public
interfaces. It starts no numerical/proof worker. Fresh output paths are
mandatory, including after failure. Run a bounded analytic route with:

~~~bash
python3 Solutions/RH080Next.v1/reproduction/reproduce_all.py \
  --context /fresh/output/context.json --run /fresh/output/analytic \
  --stages analytic-asymptotic --execute
~~~

Every selected application dependency is rebuilt. A selected-stage pass does
not mean that finite, N24 or physical stages ran.

## Full execution and resource boundary

A complete clean run is expensive. RAM and disk are checked independently:
heavy stages require at least1TiB genuinely available RAM and1TiB free disk,
an owned 300GiB/no-swap memory cgroup,256GiB host reserve, and shared scratch stop
at290GiB below its300GiB limit. Keep all run outputs on one filesystem for
immutable hardlinks. Virtual address-space ceilings are not physical RAM
commitments.

The public supervisor retains actual completed owned-resource counters,
separately from mathematical acceptance. Use the existing user manager with
a fresh service name and output directory:

~~~bash
RH080_UNIT=rh080-clean-reproduction.service
systemd-run --user --wait --pipe --unit="$RH080_UNIT" \
  --property=MemoryMax=300G --property=MemorySwapMax=0 \
  --property=TasksMax=4096 \
  python3 /absolute/repository/Solutions/RH080Next.v1/reproduction/reproduce_all.py \
    --context /fresh/output/context.json --run /fresh/output/full \
    --unit "$RH080_UNIT" --n24-workers 12 --execute
~~~

This supplies the actual command and supervisor evidence required by the fresh
N24 gate. Do not use an unrelated shared cgroup. The driver does not establish
host security policy or elevate permissions. A stopped or missing-gate stage
writes INCOMPLETE.json, preserving partial results without whole-run acceptance.

Stages execute in dependency order. Select individual names with --stages;
their dependencies are added automatically.

| Stage | Exact work |
| --- | --- |
| source-fixtures | Privately regenerate selected scalar/C/AST fixtures and compare every selected byte. |
| gaussian-inputs / gaussian | Regenerate degree80,dilation5/4 exact cell/Fourier sources; compare locked witness identities; source-cold92-module proof. |
| dual | Regenerated original source/AST and actual C stdout1221161; source-cold49-module full-CMS source-first C dual,11 theorem roots. |
| population | Regenerate two16-node C packets; source-cold91-module numerical/Fourier/ANT and matched controls. |
| analytic-flat64 / analytic-family / analytic-asymptotic | Fresh20/21/23-module kernel-only analytic routes. |
| finite-inputs | Original17-stage integer-forest producer; regenerate all34 CSV and owner Lean sources; verify byte/hash/count/width against portable manifest. |
| finite-main | Fresh681-source operational-main/numerical/finite ANT closure using regenerated34 CSV inputs. |
| canonical-finite | Canonical providers/consumers over new source-associated hardlinked dependencies; separate exact-claim gate required. |
| n24-inputs / n24-kernel | New stages24,chunk-log13,pairs-per-module524288 proposal; original1033-module checker and29 typed roots; independent actual completed resource gate. |
| n24-bank | Format-only export of the newly accepted run; no historical992/4/37 lineage imported. |
| w4-main | Actual six W4 source-main/norm/global/population/piecewise roots; exact audit marker and matched control. |
| canonical-w4 | W4/analytic providers and actual consumers; separate final canonical exact-claim gate. |
| exposure |169-common+15-locked+15-audit source replay; original3-admissible/13-censored primary statuses unchanged. |
| physical | New24 C observations in normal/-O/-OO and O0/O2/O3/UBSan; strict all-mode validation and mutation controls. Observations alone are not PV. |

Finite data regeneration stays outside the checkout. Generated owner Lean
sources are checked against existing identities before the strict data helper
builds a fresh inventory. Copying preserved CSV is not called regeneration.
N24 likewise uses the original producer and locked input. Candidate arithmetic
is an untrusted proposal until checker and actual consumers pass.

Only accepted objects produced earlier by this new run enter later associated
overlays. Linked compilers and format adapters retain source, receipt, log,
context and object identities. A format export is not a new compilation or
proof. Failed hardlinks cause failure instead of copying an80GiB dependency
bank.

## Evidence and cleanup

Each command records exact arguments, return code, elapsed time and log hashes.
Upstream pipelines supply source/object/axiom/data receipts. Actual status and
complete population are checked before stage acceptance. Only the full selected
universe can set complete_campaign_reproduction=true.

No PV/compiler claim is inferred from physical stdout. External Arb dual
proposals remain a separate tier: the dual stage reproduces the formal100/123
source-first floor, not the external2000/2399 proposal. Deterministic input/proof
replay does not reproduce nondeterministic model research or optimizer discovery.

There is no automatic deletion. After full reproduction and independent final
checks, preview and hash-check any experiment-owned regenerable large data,
redundant objects and caches before cleanup. Keep original sources, locked
inputs, accepted proof artifacts and the only reproduction copy. Retain a
minimal essential certificate if reliable regeneration is unavailable.
Root owns final bundle selection, reviewed cleanup, Git and attachment delivery.

## Bounded driver and adapter controls

These checks create fresh output directories and preserve failures. The first
runs27 actual bounded CLI cases (12 positive,15 negative) across normal, -O and
-OO; it starts no expensive proof pipeline:

~~~bash
python3 Solutions/RH080Next.v1/reproduction/test_portable_cli.py \
  --context /fresh/output/context.json --run /fresh/output/cli-controls
~~~

After the bounded analytic stage, test the linked compiler with an actual
fresh audit proof in each mode, plus21 rejection cases:

~~~bash
python3 Solutions/RH080Next.v1/reproduction/test_linked_batch_cli.py \
  --context /fresh/output/context.json \
  --bank /fresh/output/analytic/analytic-asymptotic/bank \
  --run /fresh/output/linked-controls
~~~

After all three analytic runs and the population run, test their format-only
exports in all modes. Supply each original work directory with its exact
producer context; contexts from different bootstrap locations cannot be mixed:

~~~bash
python3 Solutions/RH080Next.v1/reproduction/test_format_exports.py \
  --context /fresh/output/context.json \
  --analytic /fresh/output/full/analytic-flat64/work \
  --analytic /fresh/output/full/analytic-family/work \
  --analytic /fresh/output/full/analytic-asymptotic/work \
  --population /fresh/output/full/population/work \
  --run /fresh/output/format-controls
~~~

The12 positive exports and18 mutation controls do not compile or reprove the
exported mathematics. They reject wrong status, a Boolean in place of integer
exitcode0, and changed object identities under every optimization mode.

The canonical W4 exact-claim verifier also needs `PyYAML==6.0.3` in the
Python interpreter running this pipeline. Install it from
`reproduction/requirements.txt` in a fresh Python3.11 environment. The driver
records the actual version and stops before execution if that selected route
has a different or missing version. Plan-only mode reports the missing
prerequisite without pretending that proofs ran. Direct mathematical/kernel
stages do not acquire this package dependency unless the canonical W4 route
is selected.

The fetch branch isolates both Mathlib archive cache and Lake artifact cache
inside the fresh workspace, checks the pinned manifest before and after cache
materialization, and uses an overall deadline (default7200 seconds). It checks
build-time Cli revision ab3a82db9fea14cf0fd7f5a2de650f4b534640af separately;
Cli is not an extra compiled generic root in the proof context.32GiB free disk
is a planning admission threshold, not a proven upper bound. Existing eight
repositories allocate8.735GiB and their object roots6.314GiB; the observed shared
multi-revision archive cache cannot be attributed to this one pin. No measured
cold-fetch duration or successful new --fetch execution is claimed here.

Fresh N24 proof launches use `dual/reproduce_fft_dag_physical_v2.py` with
explicit `--worker-virtual-as unlimited`, the unchanged original numerical/kernel
checker, and independent `verify_fft_dag_fresh_v3.py` /
`export_fft_dag_fresh_bank_v3.py` gates. Unlimited virtual address space does not
raise the physical memory allowance: the actual owned cgroup remains 300GiB,
noSwap, with the separate fresh RAM/disk admission and host/scratch reserves.
The producer's1020 generated Lean identities and937 CSV identities are compared
with `dual/evidence/W4_N24_EXPECTED_INPUTS.json` before proof compilation.

The actual W4 source-main and canonical stages use the additive v2 associated
compilers with `--memory-gib 300 --worker-virtual-as unlimited` inside that same
owned physical boundary. Canonical compilation selects only
`CanonicalW4EvolutionAudit`, rebuilding its missing transitive sources. A
separate `verify_canonical_w4_evolution_v2.py` call with the frozen
`CANONICAL_W4_BASELINE.json` must produce the exact 29-claim/disjoint-entry
acceptance; a compiler exit or source-selector receipt alone is insufficient.

See SOURCE_BUNDLE.md for the exact source-selection universe, regeneration
exclusions, all16 locked payloads and final reviewed-commit acceptance rule.

## Optional strongest external dual replay

The accepted Lean/source-first proof pipeline is separate from the stronger
external numerical dual proposals. `reproduce_external_duals.py` plans or,
with explicit `--execute`, reruns their two DFT and two independent non-FFT
complex-Horner checks from fixed published-in-project inputs. It requires
Python3.12.9 and `requirements-external-duals.txt`, pins the exact source and
witness bytes, and never labels the results as Lean/PV/network acceptance.
See `../dual/README.md` for exact caps, inverses, profile distinctions and
recorded precision parameters. Plan-only controls were run in all three
Python optimization modes; no additional heavy replay is claimed merely
because this wrapper was authored.

## Immutable exposure payloads versus active acceptance

The preserved original model submission
`ablation/review/primary_locked_payloads/fixed_width-B_named-r1/check.py`
contains Python `assert` checks. Its bytes are locked historical evidence;
it is not an acceptance validator, is not invoked by the reproduction
acceptance path, and does not become source-first PV by being bundled.
The active exposure route runs
`ablation/review/reproduce_clean_proofs.py`:169 common modules,15 exact locked
transfer modules and15 independent audit modules are compiled and compared.
Its independent type/axiom/dependency validators use explicit checked errors
and run under normal Python, `-O` and `-OO`. The historical submission is
retained unchanged; no current success is inferred from its assert-only
checker or from a plan/exit status alone.
