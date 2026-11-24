# Accepted fixed count and source-run proof

Checkpoint snapshot: 2026-11-24T13:17:12.633454+00:00. The final release status will be supplied
separately after the running 30-case study finishes.

The exact fixed result is **π(1,490,000,000,000) = 55,206,486,339**. The
unchanged mathematical count, all 2,768 pure arithmetic parts, source-cold
data/gaps, unchanged Final and the actual-source-indexed modeled-output consumer
have now compiled and passed their full original acceptance readers.

This is an additive checkpoint after the historical 09:11 status document.
That document is retained unchanged. The high result was pending then and is
accepted now. Original research outcomes, C sources, numerical parameters,
mathematical assumptions and old receipts remain unchanged.

**Final supplemental controls and real-π appendix:** the additional same-input
IEANTN real-π adapter and its 24 CLI controls now pass. Its first elaboration
failure is preserved separately. The 30 completed-result cold CLI controls were
launched at 13:02:07 UTC after that author's explicit exclusive-window release;
their result remains pending. Do not infer their completion from the accepted
mathematical proofs or from the separate 24-case study.

## What the actual proof uses

The current campaign supplied 2,469 arithmetic leaves and 40 helper modules.
The source-cold stage rebuilt the 695 old numerical data/gap modules and checked
all 695 object hashes against the old identities before proof transport. That
stage has 696 declared source targets after the existing checker is included,
and 697 actual compiler records after its generated audit is included.

The last stage rebuilt all 299 previously missing arithmetic leaves plus six
final/model/audit modules: 305 actual compiler records. Its source-only transport
rejects all original 994 application objects. Historical pathnames identify
fresh byte-identical data objects; they do not cause the original bank to be
opened or admitted. The union of 2,469 and 299 disjoint arithmetic leaves is
exactly the locked 2,768-part workload.

The exported `CountSourceFinal.lean` proves the fixed `Nat.primeCounting`
equality and an inhabited execution of the two actual C texts with the modeled
output `wordBytes 55206486339`. Its universal output theorem covers every
successful modeled execution. The high C main writes **eight raw little-endian
bytes**, not decimal text. The output theorem consumes the actual numerical
Final and the independently specified bounded C syntax soundness through
formal proof values. The actual audit has 23 checked proof-value edges and
exactly 12 required source/count endpoints; an import alone is insufficient.

All 2,768 numerical arithmetic leaves have empty axiom lists. The selected
source/model consumer roots use only `propext`, `Classical.choice` and
`Quot.sound`. No `native_decide` execution axiom, new axiom or `sorry` is admitted
to this selected final chain. `PROOF_CENSUS.json` extracts the original complete
record identities and the 13 final theorem audit rows; the original compiler
stdout and all three exact small consumer sources are also included.

## Actual evidence and measured resources

| Accepted stage | Full external GNU wall | Maximum child RSS, bytes | Exact receipt |
| --- | ---: | ---: | --- |
| Resumed fixed count | 3:41:35 | 33,623,289,856 | `7af53640056a870b6cfb3e35b663b61b1e51916ce619e3a8c377eb7a9458d5f1` |
| Source-cold data/gaps | 1:31:53 | 41,635,209,216 | `12c2e559748967c7a06ab001731a3f2fd140d9dc51e427f60014eab5fe819720` |
| Fresh 299 plus consumers | 1:08:19 | 33,391,890,432 | `e4c4c64102fcd6b598d0c1cb58f6abca38e9a67f0d42cf14c60faae1827577d0` |

GNU wall includes each controller's final acceptance readback. Internal
controller seconds have narrower scopes and are recorded separately. Maximum
child RSS is not simultaneous aggregate RAM. The resumed count's sampled
aggregate RSS was 591,158,431,744 bytes; its sampled PSS was 445,180,121,088 bytes.
For the last 305 stage, internal aggregate RSS/PSS and the independent broader
outer-process sampler have different scopes; both exact records are preserved
in `RESOURCE_SUMMARY.json`. Neither is an exact physical peak measurement.

The original cold sampler missed children launched from worker threads. Its
incomplete evidence is preserved. The corrected all-thread sampler starts at
10:23:47 UTC, after the first raw-source dispatch, and therefore is not a
whole-interval aggregate measurement. Actual sampling intervals include proc
scans and are not exactly one second. Per-child GNU peaks are independent of
that sampler. No owned compilation OOM or unattributed SIGKILL was observed in
these accepted stages; unavailable kernel-wide OOM attribution remains unknown.

`EVIDENCE_EXPORT.json` distinguishes the raw cold DATA_RESULT file hash above
from the historical semantic hash
`fc98082418e883a7b5cbd24cf076497fba5391fa1248e8a184324d9b976dd30b`.
The latter hashes `json.dumps(json.loads(DATA_RESULT.read_text()),
sort_keys=True).encode()` with Python's default separators and no newline. It
is not the raw file SHA. Raw accepted receipts and source/log hashes are copied
without changing their bytes. `export_evidence.py` packages evidence only; it
does not replace any mathematical acceptance reader.

The concise census and resource tables can be regenerated using only the
exported raw receipts:

```sh
python3 Solutions/RHOcticPush.v1/ramanujan/count-feasibility/final-completion-v1/summarize_evidence.py
```

Run this from the accompanying publication source root. Actual normal, `-O`
and `-OO` executions reproduced both files byte-for-byte. This small packaging
check neither reruns Lean nor supplies a mathematical premise.

## Clean reproduction

Use the evidence bundle's standalone `finite/PACKET.json` and `finite/project/`
source packet, which has 130 pinned files. It has actual C/model/grammar source,
the deterministic numerical generator, pure checker, all Python imports,
compiler/toolchain metadata, generic bootstrap and nine exact dependency pins.
It contains no historical application objects or generated high-data bank.

Use Linux x86-64, Python 3.11, Git, GNU time, taskset/prlimit and the exact Lean
4.34.0-rc2 compiler from `project/lean-toolchain`. From `finite/project/`:

```sh
python3 Solutions/RHOcticPush.v1/integration/continuation/bootstrap_generic.py \
  --compiler /absolute/pinned/toolchain/bin/lean --cpu 64 \
  --out /large/fresh-owned/generic

python3 Solutions/RHOcticPush.v1/ramanujan/count-feasibility/portable-source-run/reproduce.py \
  --context /large/fresh-owned/generic/GENERIC_CONTEXT.json \
  --out /large/fresh-owned/finite-high --jobs 22 \
  --cpus 64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85

python3 Solutions/RHOcticPush.v1/ramanujan/count-feasibility/portable-source-run/reproduce.py \
  --check /large/fresh-owned/finite-high
```

Choose actually available CPU IDs and fresh experiment-owned directories. The
bootstrap fetches only the nine pinned generic repositories and official
generic Mathlib cache. No IEANTN application proof bank is supplied. Full
reproduction regenerates the unchanged 90,670,946-record numerical workload,
all locked source identities, all gaps, all 2,768 arithmetic leaves and the
same final count/source-output statements. No random seed is used. The full
portable front door is prepared and independently reviewed; it has **not** been
run a second time at high input. The actual high acceptance above is the
composed current-campaign/cold route, whose incremental historical schedule
requires its current-campaign receipts and banks. These two evidence claims
must remain separate.

For an actually executed bounded workflow control, use fresh paths and replace
the full command with `--smoke --jobs 1 --cpus 64`. This proves only π(1000)=168
and the original high-input program's parameterized source/model theorem. Its
60-source proof passed, as did 51 CLI controls in normal, `-O` and `-OO` modes.
The exact high-count argument remains explicit in that small proof; it cannot
be admitted as a completed high-input numerical result. The relocated
130-source packet also checked the existing small result with a file-open
trace and no old application banks; this was not a second proof compilation.

Inspect available RAM and free disk independently before starting the full
command. Its initial engine admission requires genuinely available 1 TiB RAM,
keeps a 512 GiB host reserve and adapts at most 22 lanes to measured physical
growth. Each arithmetic compiler has a 128 GiB address ceiling; large final
audits have 256 GiB. These are virtual limits, not measured RAM usage. Free disk
must separately exceed 1 TiB; at most 300 GiB of owned scratch is authorized.
Do not fabricate availability or revive a 4 GiB limit.

## Remaining trust and mathematical scope

The original compiled source/model chain reaches an exact `Nat.primeCounting`
point and exact modeled bytes. The separately accepted
`RHOcticPush.IEANTNCount.primeCounting_fixed_point` now reaches the existing
`IEANTN.primeCounting` vocabulary at this same input. Its exact-target and
33-edge audit consumes the source-run proof, independent grammar, actual
source-function correctness and bounded byte injectivity; this is not an
import-only or conjunction-only adapter. Its own four-source receipts and
24-case controls are documented in the sibling `ieantn-consumer` supplement.
This creates no new numerical point. Canonical-node registration, full finite
Ramanujan coverage and an analytic Ramanujan conclusion remain outside this
finite-point result; they must not be inferred from the adapter or its imports.

The independent theorem proves bounded C surface-syntax correspondence for
the actual two sources, including the supported preprocessing profile. It is
not a general ISO-C typing, binding or semantic-adequacy theorem. Correct
application of the restricted C execution model, pinned generic compiler and
runtime, ABI, stdio/OS and hardware remain documented contracts. The actual
native run's byte observation agrees, but it is not a formally modeled physical
machine trace. Kernel-only arithmetic or certificate checking alone is not
source-first PV; the source/model/correctness/consumer links must be assessed
with these explicit boundaries.

The 130-file packet regenerates large data instead of archiving it. We removed
only 1,476 double-hash-checked duplicate source files from unused preparations,
freeing 16,907,546,624 allocated bytes. Original research sources, locked inputs,
all accepted proofs, unique certificates and essential receipts remain. No
original worker or unrelated workspace was modified or stopped.
