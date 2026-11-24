# Read and reproduce the RH research release

Open `reports/RH_OCTIC_RESEARCH_EN.html` for the results, full assumptions,
comparisons and limitations. `reports/RH_OCTIC_RESEARCH_KO.html` presents the same
mathematics in Korean. `reports/RH_OCTIC_PAPER_EN.html` keeps the mathematical
argument together. Each HTML file works offline:
its mathematics and font are embedded, with no extension or CDN required.

The release status and receipts determine which computations actually finished.
An executable reproduction recipe alone is not a completed experiment. RH and
the named general literature inputs remain explicit mathematical assumptions.

## Download and extract

Download `EVIDENCE_PARTS.json`, `reassemble_evidence.py` and every listed part
into one directory. In that directory run:

```sh
python3 reassemble_evidence.py --parts EVIDENCE_PARTS.json \
  --out RH_LIMIT_BREAKTHROUGH_EVIDENCE.zip
```

The output ZIP must not already exist. Success prints `PASS`, the byte count
and the complete SHA-256. A missing or changed part produces an error and no
completed ZIP. Download that part again and use a fresh output filename. The
script preserves all downloaded parts. Extract the resulting ZIP normally.

The extracted directories serve different purposes:

* `reports/` contains the readable research reports and paper.
* `analytic/` is the exact immutable packet for the 739-module analytic union.
* `finite/` is the standalone source packet for the C counter and its proofs.
* `publication/` contains the reviewed source snapshot, ledgers and supporting
  evidence. It is an explicit selection from the repository, rather than a
  complete Git clone.

The bundle manifest lists every file, size, role and hash. From the extracted
root, check those identities before starting an expensive run:

```sh
python3 -B publication/Solutions/RHOcticPush.v1/scripts/verify_evidence_bundle.py \
  --root .
```

This checks artifact identity. Mathematical acceptance requires the proof and
source-program commands below. Keep the outer manifest and final status file.

## Prepare the pinned mathematical environment

Use Linux x86-64, Python 3.11, Git, GCC, GNU `time`, `prlimit` and `taskset`.
Install the Lean version in `analytic/source/lean-toolchain`:
Lean 4.34.0-rc2. The scripts also check the compiler's exact SHA-256 and all nine
generic dependency revisions, including Mathlib
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`.

Choose a fresh experiment-owned scratch parent, the pinned Lean executable and
an available CPU and an available CPU list. In the following commands replace
the four example values; the single CPU must belong to your selected list:

```sh
RH_SCRATCH=/absolute/path/to/experiment-owned-scratch
RH_LEAN=/absolute/path/to/pinned/toolchain/bin/lean
RH_CPU=64
RH_CPUS=64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85
mkdir -p "$RH_SCRATCH"
export PYTHONDONTWRITEBYTECODE=1

python3 -B analytic/source/Solutions/RHOcticPush.v1/integration/continuation/bootstrap_generic.py \
  --compiler "$RH_LEAN" --cpu "$RH_CPU" --out "$RH_SCRATCH/generic"
export IEANTN_GENERIC_CONTEXT="$RH_SCRATCH/generic/GENERIC_CONTEXT.json"
```

The bootstrap fetches the pinned public generic sources and official generic
Mathlib caches, verifies their identities and actually imports Mathlib. It does
not use historical IEANTN application objects. Preserve the resulting context
unchanged through a run and its subsequent readback.

Inspect available RAM and free disk separately. The high-resource recipes keep
512 GiB for the host; their full numerical startup requires genuinely available
1 TiB RAM. The separate disk prerequisite is 1 TiB free, with at most 300 GiB
owned scratch. A per-compiler address-space ceiling is not a measurement of
physical RAM. The recorded receipts distinguish child RSS, aggregate RSS/PSS,
disk scope, elapsed time, interruptions and OOM evidence.

## Reproduce the analytic mathematics

Install `mpmath==1.3.0` for deterministic proposal regeneration. From the
extracted root:

```sh
python3 -B analytic/source/Solutions/RHOcticPush.v1/integration/continuation/regenerate_moments.py \
  --out "$RH_SCRATCH/moments"

python3 -B analytic/source/Solutions/RHOcticPush.v1/integration/continuation/finish_clean_single_lane.py \
  --source-packet analytic --context "$IEANTN_GENERIC_CONTEXT" \
  --primary "$RH_SCRATCH/primary454" --out "$RH_SCRATCH/analytic723"

python3 -B analytic/source/Solutions/RHOcticPush.v1/integration/feedback/reproduce.py \
  --foundation "$RH_SCRATCH/analytic723/ram60611" --out "$RH_SCRATCH/feedback734"
python3 -B analytic/source/Solutions/RHOcticPush.v1/comparisons/reproduce_box_lee.py \
  --foundation "$RH_SCRATCH/analytic723/ram60611" --out "$RH_SCRATCH/box-lee725"
python3 -B analytic/source/Solutions/RHOcticPush.v1/comparisons/reproduce_nl_parabolic.py \
  --foundation "$RH_SCRATCH/feedback734" --out "$RH_SCRATCH/nl737"
```

The first command reproduces all 128 generated Lean files and three proposal
JSON files. Those are untrusted proposals until checked by the Lean kernel.
The remaining commands compile the complete mathematical consumers and audit
their actual proof dependencies. Their source sets overlap: the union has 739
compiler module identities, including auditors and adapters.

The `box40` historical phase label contains 40 scientific modules and one
auditor, hence 41 actual compiler modules. Use the explicit phase inventory
when reproducing totals. For readback and the actual optimization-mode control
commands, follow `analytic/source/Solutions/RHOcticPush.v1/integration/continuation/README.md`.

Each output directory must be new. A failed or interrupted attempt remains a
separate record; do not rename it as accepted or overwrite it. The fresh route
above does not require the original failed run. The recorded historical prefix
recovery has its own precise provenance and is not an uninterrupted execution.

## Reproduce the finite source-program route

Read the accompanying finite status and reproduction document first. It
distinguishes the accepted bounded control, any completed high-count proof,
the historical cold-complement schedule and the full clean-source recipe.

From the extracted root, a bounded source/model control is:

```sh
python3 -B finite/project/Solutions/RHOcticPush.v1/ramanujan/count-feasibility/portable-source-run/reproduce.py \
  --context "$IEANTN_GENERIC_CONTEXT" --out "$RH_SCRATCH/finite-smoke" \
  --smoke --jobs 1 --cpus "$RH_CPU"
```

This bounded control proves only the count at 1000 and the original high
program's parameterized source/model consumer. It does not substitute a weaker
numerical target for the high experiment. To regenerate the full locked
90,670,946-record workload, every arithmetic check, final count and source-indexed
output consumer, use a separate fresh directory and the adaptive worker limit:

```sh
python3 -B finite/project/Solutions/RHOcticPush.v1/ramanujan/count-feasibility/portable-source-run/reproduce.py \
  --context "$IEANTN_GENERIC_CONTEXT" --out "$RH_SCRATCH/finite-full" \
  --jobs 22 --cpus "$RH_CPUS"
```

Use a comma-separated list of allowed CPU IDs. The example supplies 22 IDs;
choose at least as many distinct IDs as `--jobs`, or lower `--jobs` for a shorter
list. Twenty-two is a maximum, not a forced concurrency. The controller checks
actual resources and preserves the host reserve. Once that full high run is accepted,
append the same-point source-byte proof and the actual IEANTN prime-counting
consumer from the publication source:

```sh
python3 -B publication/Solutions/RHOcticPush.v1/ramanujan/count-feasibility/ieantn-consumer/reproduce.py \
  --basis "$RH_SCRATCH/finite-full" --basis-kind portable-full \
  --context "$IEANTN_GENERIC_CONTEXT" --out "$RH_SCRATCH/ieantn-point"
python3 -B publication/Solutions/RHOcticPush.v1/ramanujan/count-feasibility/ieantn-consumer/test_controls.py \
  --run "$RH_SCRATCH/ieantn-point" --out "$RH_SCRATCH/ieantn-controls"
```

The append rebuilds the existing IEANTN vocabulary, bounded byte-injectivity
lemma, real-function consumer and proof audit. Its full-high gate rejects the
1000 control as a basis. All 24 controls have distinct logs across normal,
`-O` and `-OO` modes: three real positive readbacks and 21 specific negative
metadata/source/output cases. Parent validators refresh dependency-probe logs,
so run these commands serially rather than sharing one basis between concurrent
readbacks.

The actual accepted high-result campaign combined current-campaign arithmetic
with the freshly rebuilt cold complement, then used its accepted 305-module
basis for the four-source append. The bounded clean-source control and the
high-basis rejection controls were executed separately. The monolithic full
clean-source high sequence above is a deterministic reproduction recipe; it
was not executed as an additional uninterrupted high campaign. The immutable
finite130 packet alone does not include the later four-source IEANTN append.
Read the final receipts for the actual acceptance and resource measurements.

To reproduce the ordinary compiled C observation independently, run:

```sh
python3 -B publication/Solutions/RHOcticPush.v1/ramanujan/count-feasibility/high-driver/run_native_high.py \
  --out "$RH_SCRATCH/native-high" --cc gcc-11 --cpu "$RH_CPU"
```

This compiles the two unchanged C sources and records compiler, executable,
output, timing and RAM identities. The recorded compiler is GCC 11; its precise
version and binary hash are in the execution receipt. The eight bytes decode
to 55206486339. The native helper's historical status labels describe an
ordinary observation, not acceptance of the complete source-first chain.
The separate source/model correctness, exhaustive kernel witness and final
IEANTN consumer establish the mathematical connection. No physical execution
trace or formal C-compiler correctness theorem is claimed.

Independent restricted C syntax, formal execution correctness and mathematical
output linkage are separate from generic C-model applicability, compiler,
headers, ABI/runtime, stdio/OS and hardware contracts. Kernel-only numerical
certificates and native observations are not called source-first PV.

## Rebuild the readable reports and retain evidence

Report generation uses ordinary desktop resources. The recorded renderer uses
Node 20.20.0 and locked KaTeX 0.16.47. From the extracted root, in the same
terminal, install its packages into owned scratch and keep the downloaded
source tree unchanged:

```sh
mkdir -p "$RH_SCRATCH/report-renderer"
cp publication/Solutions/RHOcticPush.v1/reports/rendering/package.json \
  publication/Solutions/RHOcticPush.v1/reports/rendering/package-lock.json \
  "$RH_SCRATCH/report-renderer/"
npm ci --ignore-scripts --no-audit --no-fund --prefix "$RH_SCRATCH/report-renderer"
python3 -B publication/Solutions/RHOcticPush.v1/reports/build_reports.py \
  --status publication/Solutions/RHOcticPush.v1/reports/FINAL_STATUS.json \
  --katex "$RH_SCRATCH/report-renderer/node_modules/katex" \
  --out "$RH_SCRATCH/rebuilt-reports"
```

Use the accompanying final release status file for final report text. Report
manifests give the exact hashes; delivered aliases, if any, contain identical
bytes. The rendering README gives the same package pins for repository use;
its `Solutions/...` commands assume the repository root as working directory.

Keep the source, parameters, dependency pins, commands, final statements,
accepted receipts and artifact hashes. There are no random seeds. Large prime
lists and numerical intermediates are deterministically regenerated rather
than required as permanent downloads. Delete only previewed experiment-owned
duplicates after checking regeneration; preserve original research, locked
inputs, unique certificates and accepted proof artifacts.

The official IEANTN Comparator workflow receipt is a separate acceptance step.
It requires the approved verification environment and a compatible worker.
Local Lean kernel, axiom, source and dependency receipts do not impersonate
that workflow receipt.
