# Reproduce the QRH experiments

Read [the status/assumption handoff](README.md) first, including its rendering correction. Use [FORWARD_REPORT.html](FORWARD_REPORT.html) for the corrected readable full forward report; original companion artifact hashes still refer to their immutable originals. Commands below run from a
clone of `hs-chae/IEANTN_test` on branch `qrh-2pv`, unless a different directory is
shown. They are reproduction instructions, not claims of a fresh cold replay in
this documentation-only publication.

## Prerequisites and pins

Use Elan/Lake, Python 3 with the repository's declared development requirements,
and GCC for optional native diagnostics. Internet access is needed to obtain the
pinned external Lean packages/toolchains when not cached. Solution builds can be
substantial. Existing source-identical same-pin caches were used in the recorded
checks; new users need their own dependencies.

| Environment | Lean | Mathlib |
|---|---|---|
| Canonical checkout and every `Solutions/*` project | `leanprover/lean4:v4.34.0-rc2` | `71a80585ee495fc24472fd0eaffc89d94e4fd8d6` |
| Separate actual published QRH replay | `leanprover/lean4:v4.34.1` | `d13f23b723b8a846827a245b89c10fc7d3f11612` |

The foreign replay is not a canonical solution-toolchain upgrade. Never copy
`.olean` files across these environments. The actual source artifact includes
its compatible CH2 routing ports, selected source closure and licenses.

## 1. Core and metadata

```bash
git clone --branch qrh-2pv https://github.com/hs-chae/IEANTN_test.git
cd IEANTN_test
python3 -m venv ../ieantn-qrh-tools
../ieantn-qrh-tools/bin/python -m pip install -r requirements-dev.txt
lake exe cache get
lake build
../ieantn-qrh-tools/bin/python scripts/ieantn.py gen-challenges --check
../ieantn-qrh-tools/bin/python scripts/ieantn.py fingerprint --check
../ieantn-qrh-tools/bin/python scripts/ieantn.py check
```

One generated-challenge `sorry` warning per conclusion is expected; challenges
state the problem. Do not remove those placeholders or treat a core build as a
solution proof. At the documented snapshot, the last command exits 1 for the 49
inherited upstream-vs-fork receipt provenance errors described in the handoff.
That is a disclosed non-passing full check, not permission to ignore new errors.

## 2. Canonical Table 4 pair

Run each block from the repository root:

```bash
(cd Solutions/FKS2Numerics.v6 && lake update && lake build)
(cd Solutions/FKS2Numerics.v7 && lake update && lake build)
(cd Solutions/FKS2.v9 && lake update && lake build)
```

`FKS2Pair.assembled` supplies both program proofs and their consumers, but still
has an explicit QRH argument and the named analytic/anchor inputs. The separate
compatible replay supplies the actual QRH proof. The generic profile transport
retains fixed 30-cell geometry.

## 3. Canonical forward pilot and kernel alternative

```bash
(cd Solutions/RamanujanNumerics.v1 && lake update && lake build)
(cd Solutions/RamanujanNumerics.v2 && lake update && lake build Solution ForwardRamanujanUpdate.Grouped ForwardRamanujanUpdate.KernelSource)
```

The second command explicitly checks the optional grouped instances and kernel
alternative, not only the main `Solution` import. It can take longer because the
kernel-only complete source-match computation is expensive.

To inspect the exact implemented theorem and axiom closure:

```bash
cat > /tmp/QRHForwardPreview.lean <<'LEAN'
import ForwardRamanujanUpdate.Assembly
import ForwardRamanujanUpdate.Grouped
import ForwardRamanujanUpdate.KernelSource
#print ForwardRamanujan.forward
#print axioms ForwardRamanujan.forward
#print axioms ForwardRamanujan.grouped_old
#print axioms ForwardRamanujan.grouped_new
#print axioms ForwardRamanujan.KernelSource.source_guard
#print axioms ForwardRamanujan.KernelSource.certified_upper
LEAN
(cd Solutions/RamanujanNumerics.v2 && lake env lean /tmp/QRHForwardPreview.lean)
```

Expected: main paired source endpoint has 12 finite native facts plus the three
standard axioms; each grouped endpoint has six; the kernel source guard has only
the standard three; its reconstructed upper bound has five finite native facts.
Canonical `ForwardRamanujan.forward` has one used refined-psi hypothesis. These
are source-associated checked paths, not official three-axiom compliance.

## 4. Optional GCC diagnostics

The C programs only evaluate their numerical allowance, not the prime-counting
function itself. From the repository root, use fresh binaries outside the source:

```bash
mkdir -p /tmp/qrh-forward-c
cc -std=c11 -O0 -fno-fast-math -ffp-contract=off Solutions/RamanujanNumerics.v1/c/baseline.c Solutions/RamanujanNumerics.v1/c/harness.c -lm -o /tmp/qrh-forward-c/old
cc -std=c11 -O2 -fno-fast-math -ffp-contract=off Solutions/RamanujanNumerics.v2/c/updated.c Solutions/RamanujanNumerics.v1/c/harness.c -lm -o /tmp/qrh-forward-c/updated
/tmp/qrh-forward-c/old
/tmp/qrh-forward-c/updated
```

Expected bits: old `40ae95302f2fc329`, updated `4022338dd9402a60`. The harness
checks binary64/unsigned-width and round-to-nearest preconditions. Native output
agreement is a diagnostic; the Lean proof additionally consumes the actual
source-token, load, execution, domain and FP-error certificates. Compiler/runtime
and hardware correctness remain trusted.

## 5. Actual OpenAI QRH replay and full acceptance artifacts

**These companion packages are not inside this canonical Git checkout.** See
[ARTIFACTS.json](ARTIFACTS.json) for names, sizes, SHA256 values and the exact owner
channel messages where they were delivered. Do not report a missing package as a
failed theorem or invent a replay. Obtain the named artifact from the owner if
your environment lacks access. The published source commit history is now in
this branch; older reports saying the commits were local describe their earlier
snapshot, not the state after this authorized push.

For a full recorded experiment, obtain all five ZIPs plus its standalone
acceptance JSON, verify their hashes, and extract all ZIPs into one fresh directory
with Python `zipfile` or another ZIP/LZMA-capable extractor. The forward source
snapshot materializes 11 Git file aliases; its source inventory records the
original modes/targets. No cross-compiler objects are shipped.

For the forward artifacts, from that extracted directory:

```bash
python evidence/restore_manifest.py /path/to/IEANTN_FORWARD_ACCEPTANCE.json
python evidence/validate_forward.py --root . --output /tmp/qrh-forward-evidence.json
cd replay-source
lake update
lake exe cache get
lake build ActualForward
```

The validator checks recorded input/evidence/artifact associations and all nine
routes. **It does not rerun Lean.** The final command is the actual compatible
source-replay build; it supplies the real OAI theorem and leaves 13 explicit CH2
hypotheses, each used. A fresh cold relocated build may need significant time;
the recorded source-overlay check reused same-pin inherited libraries.

For the earlier Table 4 artifact, use its `READ_EXTRACT.txt` and acceptance carrier;
the compatible root is `ActualPair` and the paired theorem leaves 18 hypotheses.
The source archives contain the selected full source closure, licenses and source
maps, so a new replay does not depend on unpublished local Git objects.

## After changing a mathematical source

Use the normal IEANTN contribution workflow. Recheck the changed solution targets,
exact theorem types, axiom closure and actual source/provider dependencies. A new
source literal or generator run needs a new associated certificate. Regenerate
challenges/fingerprints where appropriate, preserve old versions, and rerun the
relevant mutation controls. Validators must stay effective under Python normal,
`-O`, `-OO`, `PYTHONOPTIMIZE=1` and `PYTHONOPTIMIZE=2`. Never promote local research
acceptance to a workflow-issued receipt.
