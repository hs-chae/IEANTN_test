# Clean-environment reproduction

The preserved source-identical retry used the process-only page policy
in [PROCESS_RESOURCE_PROFILE.md](PROCESS_RESOURCE_PROFILE.md) and later hit
the physical300GiB limit. The accepted compact proof assembly is a separate
proof-only repair with unchanged numerical source, payloads and claims. Apply that
wrapper outside the whole coordinator/supervisor before compiler version or
context checks, including a real bootstrap fetch. The numerical C source and original
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
result. Missing W4/canonical interfaces stop the driver with an explicit
incomplete receipt. Bounded current private CLI plans report zero missing
interfaces. This counts only listed entrypoints and locks; it does not establish
the complete transitive runtime closure or execute proofs. Complete bundle
coverage rests on the full source/runtime inventories, typed source/data
regeneration recipes and actual component runs. The actual associated W4 Main
source-first chain and the local canonical29-claim/38-root/8-route gates have passed.
The separate posthoc fully kernel control has also passed. The normal repository build and fingerprint generation succeeded. Seventeen
of23 commands passed; six inherited receipt-provenance checks failed in the
local clone context. Official Comparator statuses are unchanged. This driver does not rewrite collaborator proof statuses.

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
  python3 /absolute/repository/Solutions/RH080Next.v1/pv/generic_page_policy_exec.py \
    --disable-thp --receipt /fresh/output/PROCESS_POLICY.json -- \
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
| n24-inputs | Original stages24,chunk-log13,pairs-per-module524288 producer; all1020 original generated Lean and937 CSV identities remain fixed. |
| n24-compact | Source-only derivation changes two Final proof bodies and adds two helpers, preserving original PLAN, numerical data and31 public declaration headers. This is an untrusted proposal. |
| n24-kernel | Unchanged original checker over the derived candidate:1035 source-cold mathematical providers and29 original typed roots; independent actual completed resource gate. |
| n24-bank | Format-only export of the newly accepted run; no historical992/4/37 lineage imported. |
| w4-main | Actual six W4 source-main/norm/global/population/piecewise roots; exact audit marker and matched control. |
| canonical-w4 | W4/analytic providers and actual consumers; separate final canonical exact-claim gate. |
| c7-kernel-control | Three fresh public proof/audit modules, same scalar caps, N24 norm and ANT consumer; full kernel non-PV proof-value control with exact PV/control type comparisons and Std3 audit. This is a separate posthoc control, not the FFT-layer-only control. |
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
cold-fetch claim is inferred from planning. A later actual supplemental fetch
completed in71.440s, independent fresh-context validation in0.340s, and all23
source-cold analytic modules/15 Std3 theorem roots in102.089s. The outer
coordinator completed in177.132s with actual completed OOM/kill0/0. Its
independent receipt is `bootstrap-real-fetch-v4/INDEPENDENT_ACCEPTED.json`.
The fresh generic roots and their build/cache infrastructure remain trusted;
this is neither source-first PV nor a new full681/1035-module clean replay.

Fresh N24 proof launches use `dual/reproduce_fft_dag_physical_v2.py` with
explicit `--worker-virtual-as unlimited`, the unchanged original numerical/kernel
checker. The additive `compact-proof-repair-v1/tools/verify_fresh_compact.py`
and `export_fresh_compact.py` gates invoke the unchanged independent fresh
checker/gate contracts and additionally pin the approved compact source identities. Unlimited virtual address space does not
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

## Original numerical inputs and compact proof assembly

The original `dual/evidence/W4_N24_EXPECTED_INPUTS.json` remains an immutable
1020-generated-Lean/937-CSV history. The driver first regenerates and checks
those exact bytes. The separate `n24-compact` stage executes:

~~~bash
python3 Solutions/RH080Next.v1/compact-proof-repair-v1/tools/derive_compact_candidate.py \
  --candidate /fresh/output/full/n24-inputs/work \
  --out /fresh/output/full/n24-compact/work \
  --project-root Solutions/RH080Next.v1
~~~

The derived PLAN remains UNTRUSTED. It contains1022 generated modules: original
numeric modules with two approved Final proof bodies, plus TopShapeSymbolic and
NormSymbolic. The original twelve mathematical foundations and the exact original
29-root audit complete1035 mathematical providers. A diagnostic import probe
is excluded from that count. This repair changes proof assembly, not the C
program, arithmetic algorithm,937 CSV payloads, numerical statement, analytic
assumptions or downstream theorem types.

Derivation and format export are not source-first PV. The actual kernel checker,
independent source/resource gate and actual Main source-to-execution-to-ANT
consumers must still pass in a fresh run. The recorded accepted lineage reuses
1031 previously validated numerical modules and compiles four proof modules;
it is not a monolithic new1035-module replay. The portable clean route is fully
specified, but its new heavy1035/681 replay has not been claimed completed.

The bounded CLI coverage for the additive driver comprises9 positives and12
negative cases in normal Python, -O and -OO; unowned execution is rejected before
an application stage. The compact contract has separate all-mode source/mutation
controls. None of these counts includes a full heavy clean replay.

## Supplemental bootstrap resource accounting

The original two real fetch attempts failed their resource-monitor observation
route before producing an accepted fresh context; they are not mathematical or
dependency failures. Retain both histories. The additive quiescent resource guard
pauses only its owned child lineage around complete disk scans and always resumes
it, retaining the physical300GiB/noSwap, host256GiB reserve, whole-campaign288GiB
stop and1200-second deadline. Its optional workspace cap is bounded1..24GiB,
default24; the prepared fetch profile uses22. Whole campaign and workspace paths
must both lie under the same owned scratch root. Counts are sampled, not exact
instantaneous peaks. A resource completion is not proof acceptance.


## Normal repository CLI and retained native cache

The actual normal workflow runs `lake build IEANTN ieantn_hash`, generates
fingerprints once, and runs seven strict checks in normal Python, -O and -OO:
`fingerprint --check`, `check-graph`, `check-closure`, `check-pins`,
`gen-challenges --check`, `check-receipts`, and final `check`. Source and old
26-file node baselines are preserved; STATE/GRAPH views are not rewritten.
The phase runner records GNU time and maximum RSS per actual command, plus
final binary, core object and hash-source identities. This metadata workflow
is separate from local mathematical proof acceptance and official Comparator.

The first native build reached its1200-second generic wall bound before
finishing; the completed guard recorded zero OOM/OOM kills. Its mixed
4-to32-CPU timing is not a controlled performance comparison. Native caches
and all first-run evidence were retained. The additive generic resource guard
v4 permits an explicit wall bound up to7200 seconds, default1200, preserving
the owned physical300GiB/noSwap, host256GiB reserve, initial cap bounded at280,
strict initial plus workspace below288GiB, and runtime288GiB stop. The
continuation uses the existing native prefix and new receipts; it does not
retroactively make the interrupted first build a success.

After the actual bootstrap/23-module reproduction was independently checked,
8865 single-link downloaded generic-cache archives (466,849,792 allocated
bytes) were removed using an exact reviewed inventory. All eight installed
generic roots, their sources/Git, the accepted context and all23 proof objects
remain. Cache archive cleanup is neither mathematical nor source-first PV
acceptance.


### Reproduce the fully kernel posthoc control

Select `--stages c7-kernel-control` with the driver command above. Its
canonical-W4 and W4-Main dependencies run first; the unchanged linked compiler
then compiles `C7KernelAudit` and its two public mathematical source dependencies
from source. The helper already searches `pv/lean`; do not repeat that directory
with `--source-root`. The final check compares the exact theorem type to both
source-W4 and the earlier FFT-layer-only control, checks the final axiom closure,
and excludes C-source/execution providers from the audited proof-value path.
Unused source-containing module imports and elaborator I/O remain disclosed;
this does not claim a source-free module graph or a verified Lean compiler.

The historical accepted execution compiled the two mathematical modules first
and then reused those exact objects while compiling the repaired audit. A clean
driver run compiles all three anew. Bounded driver CLI tests and synthetic stage
control-flow/freshness tests are separate from that actual Lean execution. No
full new681/N24 clean-driver replay is claimed.

### Reproduce the normal repository checks

The standalone entry point is `reproduction/verify_normal_network.py`:

~~~bash
python3 Solutions/RH080Next.v1/reproduction/verify_normal_network.py \
  --repository /absolute/repository --context /fresh/context.json \
  --run /fresh/normal-checks --python /absolute/pinned-venv/bin/python
~~~

Run this inside the documented owned resource service, with the process-only
THP wrapper applied before the entire guard and phase runner. Use pinned
PyYAML6.0.3 in the selected Python environment. The runner checks nine separate
mutable package Git checkouts under the repository's `.lake/packages`, at the
revisions in the root `lake-manifest.json`. For each of its nine git package
records, clone the recorded `url` into the fresh `.lake/packages/<name>`
directory and run `git checkout --detach <rev>` using that record's exact `rev`.
Reject an existing destination, a mismatched HEAD or any dirty tracked source;
leave the root manifest unchanged. Retain real package directories and their
own build caches, without links to the
protected accepted generic-library context. The runner rejects dirty or
mismatched source revisions. Generic library/compiler/cache infrastructure is
trusted; the separate accepted context is used for dependency identity checks.

The selected per-run log/cache-directory cap excludes mutable repository package
caches. The whole-campaign unique allocation guard counts both locations and
remains authoritative. A cached continuation uses new command/result receipts
and never changes the first deadline stop into a success. Resource guard-v4
controls and preserved failed admission history are documented under
`evidence/generic-guard-v4`; they do not constitute mathematical acceptance.


## Actual ordinary repository workflow outcome

The cached continuation completed the18,647-job native build, the updated
`ieantn_hash` executable and core object, fingerprint generation, and every
planned command. Seventeen of23 commands returned0. In each of normal Python,
-O and -OO, the five fingerprint/graph/closure/pin/challenge checks passed;
`check-receipts` and aggregate `check` returned1. All49 inherited receipt files
name the public upstream repository, while the local snapshot's inherited
origin is a filesystem path. No inherited receipt, validator or mathematical
source was changed to make these checks pass. Thus the normal workflow remains
incomplete, while the separately audited mathematical results retain their
actual acceptance. This is not official Comparator approval for the owner fork.

Build/phase/outer durations were1010.190/1218.497/1228.272seconds. Completed
owned OOM/OOM-kill counters were0/0. Maximum individual command GNU RSS was
7,183,768KiB; the sampled cgroup charge15,188,430,848bytes is only a lower
bound, with no exact peak available. Independent post-execution review
rechecked65,875 protected sources, the original26-file baseline,198generated
fingerprints,53execution pins and the actual command/log/time/binary identities.
The51text source pins are retained byte-for-byte with an INDEX; the other two
generic executable payloads are represented by exact hashes. These historical
execution snapshots remain distinct from later report/documentation edits.
The first1200-second native deadline stop remains a separate failed attempt.


## Supplemental provenance, measured cleanup, and historical scouts

A separate disposable upstream checkout ran the unchanged online inherited
receipt validator in normal/-O/-OO: allthree passed for49files/20workflow runs
and their jobs in94.321seconds. All50inputs and seven shared Git configurations
were unchanged. This upstream-only supplement preserves the raw local17PASS/
6contextFAIL matrix and confers no official approval on new owner-fork nodes.

The exact cleanup removed18,662regenerable generated C/object leaves,
824,431,612logical/864,055,296allocatedleafbytes. All90,704protected proof,
interface,IR,binary andlibrary identities were retained. SerializedIR remains
a hasher runtime input. A direct post-cleanup hasher check passed in4.508seconds
with the same recorded fingerprint; all removed leaves stayed absent, so none
were rebuilt. These leaf totals are distinct from global disk changes.

The scientific evidence index maps actual accepted Gaussian92, CMSdual49,
population91, analytic20/21/23-module routes,199exposure compilers,24physical
observations/42mutation rejections,11named-source contracts and18asymptotic
audit rows to exact source/evidence members. N24 has a separate exact index
of1035original compile receipts and3105stdout/stderr/time files, three full
independent readers, and the originalAS/stall/physicalOOM histories.

The fixed-W4 native449-mesh scout(252..700) is retained with its exact original
code/result and a fresh-output-only reproduction adapter. Its best mesh remains
360; it misses0.851/0.850/0.845/0.8 and establishes no other-family or continuous
optimality claim. The original LP40 main source is hash-exactly recovered; its
local helper was not pinned by that original receipt, though the retained helper
matches the later contemporaneous fine-run pin. The record preserves this
limitation. Accepted Gaussian reproduction uses the locked rational witness
and kernel proofs, independently of repeating a floating LP optimization.
