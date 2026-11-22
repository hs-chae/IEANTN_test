# RH continuation source and evidence bundle

The `network/` tree preserves the IEANTN directory layout. It includes the
continuation's sources, reports and evidence; the canonical core; all thirteen
new node families; the eleven actual public Solutions; the historical146-module
Ramanujan/checker source package; and the C/AST/include-string prerequisites.
BoxMellinInputs and PrimeKernelInputs are open analytic leaves and have no fake
Solution. The canonical census has44 propositions:29 typed proof edges and15
explicit source/open inputs; the replay does not discharge those15 inputs.
`SOURCE_SELECTION.json` gives the exact inclusion/exclusion rule and
every selected written-source hash. The historical public English/Korean reports
are included; larger original publication history can be recovered from the
repository and exact pins in `network/Solutions/RHContinuation.v1/ledgers/`.

The mathematical claims and their remaining RH/literature/analytic inputs are
explained in the continuation reports. Source-first PV applies to the identified
C coefficient and C-log components. Kernel analytic proofs, native numerical
scouts and certificate checks retain their separate verification labels. This
bundle does not close full finite-prime-count source-first PV or the open
analytic input nodes. Original locked primary outcomes remain unchanged. Regenerable downloaded
third-party paper PDFs are omitted from this distributed archive; exact source
URLs, SHA256 values and download/review receipts remain, and original local
papers are preserved. The paper can be fetched again for any historical
evidence-manifest check; no selected Lean build requires it.

## Verify the downloaded files

Use Linux x86-64, Python3.11+, Git, a C compiler, GNU `/usr/bin/time`, and the
exact Lean4.34.0-rc2 distribution. The compiler SHA256 and generic source commits
are listed in `GENERIC_DEPENDENCY_PINS.json`; the bundled `leantar` SHA256 is in
`GENERIC_CACHE_ARCHIVES.json`. The source bundle includes no compiler distribution or precompiled generic
Mathlib libraries, and no historical application/checker object bank.

Delivery parts are at most6MiB. Download every `RH_SOURCE.partNNN`,
`PARTS_MANIFEST.json` and `join_bundle.py` into one folder, then run
`python3 join_bundle.py --parts-dir . --out RH_CONTINUATION_SOURCE_EVIDENCE_20261122.tar.gz`.
The helper checks each part and the reconstructed archive SHA256; `--check` checks
the download without writing an archive.

After extraction, run from this bundle directory:

```bash
python3 prepare_bundle.py verify --tree .
```

The archive itself has a separate SHA256 receipt. For a controlled extraction,
use the independently received `prepare_bundle.py` with `extract --archive ...
--out ...`; it rejects duplicate, escaping, linked and prefix-colliding members
before writing, then checks every file against the strict manifest. A fresh
output directory is required. Existing outputs are preserved on failure.

## Exact generic dependencies

Restore the nine source repositories using their exact URLs and `rev` values in
`GENERIC_DEPENDENCY_PINS.json` (the compiler/toolchain is separately pinned).
Put them in a directory whose children are named `mathlib`, `plausible`,
`LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`,
and `Cli`. For each repository, fetch its pinned commit, check out that commit
in a separate clean checkout, and verify `git rev-parse HEAD`. Do not replace
the manifest pins with branch heads or run an unpinned `lake update`.

For a fresh generic cache, no prior Cache executable or proof libraries are
required. Set `packages` to those nine source checkouts, `compiler` to the exact
Lean binary, and `scratch` to an experiment-owned directory on a filesystem
with room for the downloaded and reconstructed libraries. This checked route
downloads449MB of exact official archives and materializes approximately13GB
of fresh libraries and the independent transport view. It requires at least
560GiB host MemAvailable because its inherited policy reserves512GiB for the
host and admits48GiB for a job. No randomness is used.

```bash
python3 BOOTSTRAP_GENERIC.py --packages "$packages" --compiler "$compiler" \
  --out "$scratch/generic"
```

The default route downloads and SHA256-checks all8,865 official archives, unpacks
them using the pinned compiler's `leantar`, builds37 cache-missing generic tools
and one `Cli.Basic` prerequisite from the included pinned source/setup/JS inputs,
and checks every generic semantic artifact against the unchanged historical
inventory. It then creates an owned regular-file view with the exact archived
build metadata and runs the actual unchanged old146 input validator. It never
changes the source checkouts or their existing caches. All steps, failures,
commands, return codes and sampled resource records are retained in scratch.

The archival metadata is explicit: `.trace`, `.hash`, one zero-byte marker and
one47,449-byte IDE reference-usage `.ilean` file. The latter's declarations,
imports, module and version equal the fresh official file; four reference-usage
dictionaries differ. Its corresponding kernel/IR object hashes all match.
`generic-bootstrap-evidence/INEQ_ILEAN_DIFFERENCE.json` records the comparison.
This transport preserves the full old validator; it does not relax any expected
semantic object hash. Generic source/build identity and scientific source/
validator identities are recorded separately.

If the exact original generic cache already exists, it may instead be mapped
with `ramanujan/configure_context.py`; this is a cache-reuse route, distinct
from the fresh generic bootstrap above.

## Rebuild the scientific application proofs

Use the freshly produced context:

```bash
python3 REPRODUCE_BUNDLE.py \
  --context "$scratch/generic/owned-view/GENERIC_CONTEXT.json" \
  --out "$scratch/science"
```

The default rebuilds the five primary routes and both canonical-node appends in sequence: the111-source
integration and five public adapters; the46-source actual-C log closure with
all127 inputs in normal/-O/-OO numerical routes; the default146+10+8+7
Ramanujan closure and actual21-input C coefficient run, followed by the actual14-module
GM→J→prime-counting and canonical Ramanujan/RHPrimeCounting replay; the18-module
signed closure; the seven-module Mobius component closure; and the three actual
Nicolas/Mertens/Mobius canonical adapters with all six typed outputs. The default
therefore recompiles all eleven real public Solutions and audits their29 outputs. Every application
object starts fresh. The compiler uses only that run's new application objects
and the explicitly pinned generic libraries. Every component must pass its own
theorem/axiom/source gates before the bundle receipt is published.

`--component integration`, `clog`, `ramanujan`, `signed` or `mobius` selects one
route explicitly (`ramanujan` includes its canonical-node append). The explicit
`--component ramanujan-nodes --strong-run <completed-fresh-strong-run>` route rechecks and
reuses that fresh bank for the14-module append. `--component signed-nodes --signed-run
<fresh-signed-run> --mobius-run <fresh-Mobius-run>` similarly rechecks both source
directories before the three signed adapters. When reusing a completed run, pass
the exact generic context used to build it: the unchanged dependency-path audit
intentionally rejects a different path map. The default creates and consumes all
fresh runs under one shared context. `--check` performs input/source preflight only and is never
reported as a mathematical replay. Default application jobs admit80GiB each
while preserving the512GiB host reserve; the bundled runner also samples owned
process-tree RSS and enforces the job/wall limits. Jobs are sequential, within
the300GiB aggregate new-study cap. Source-level C execution and the actual
analytic theorem still have the precise trust/premise boundaries in their
component receipts. These scripts do not infer a kernel OOM counter from an
exit code; resource evidence distinguishes what was measured.

For direct component CLIs, set `PYTHONDONTWRITEBYTECODE=1` and
`IEANTN_GENERIC_CONTEXT` to the generated context. Signed and Mobius accept that
context with their `--context` argument; the archive route does not require a
Git repository at `network/`. Track-specific README files document additional
controls and supplemental comparison replays.

The nine-comparison supplement uses the exact commands in
`network/Solutions/RHContinuation.v1/parabolic/reviews/FRONTIER_SUPPLEMENT_REPRO.md`.
After the default science replay, set `RH_REPO` to this bundle's `network/`,
`RH_CHECKERS` to `$scratch/science/ramanujan/foundation/base/objects`, and
`RH_PNT` to `$scratch/science/clog/objects`; use the fresh generic context above.
Its eight point comparisons and one uniform spectral gain retain the precise
scopes in that document. They are kernel mathematics, separate from source-first PV.

`STAGED_REPLAY_STATUS.json` records the actual staged application tests. Those
five tests used the exact original external generic caches; the separate fresh
generic bootstrap receipt records independent cache assembly and the unchanged
full-byte gate. This distinction is preserved even though the resulting generic
input bytes are identical. A passing component does not discharge the explicitly
open analytic or full finite-prime-count PV obligations.
