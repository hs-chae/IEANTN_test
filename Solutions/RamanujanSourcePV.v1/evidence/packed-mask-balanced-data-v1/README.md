# Balanced representation of the unchanged P-million bitmask

This is a bounded kernel-data encoding study, not a new ANT result or new C PV.
Every encoding denotes exactly the same 1,000,000 bits at lo=38,358,837,684.
There is no random seed. The original 285 cell values and original source C are unchanged.

## Observed results

| Representation | DATA compile seconds | Equality seconds | DATA object bytes |
|---|---:|---:|---:|
| Single literal (DATA only) | 26.127 | baseline | 130,928 |
| Balanced256, scoped recursion option | 8.695 | 4.835 | 14,295,752 |
| Balanced1024 | 5.119 | 4.398 | 3,677,904 |
| Balanced4096 | 4.553 | 4.329 | 1,024,648 |
| Same4096, noncomputable DATA | 4.535 | 4.327 | 194,288 |

The last representation avoids irrelevant native code generation. Its source is
254,644 bytes versus250,169 for the single literal, and its object remains larger
than the single-literal object. This is a compilation-time improvement, not a
claim of universally smaller storage.

A separate standalone provider imports only the generic unchanged sieve and the
recommended DATA, proves its exact mask equality in110.734s, and then transfers
through the universally proved primitive-operation identity. Its observed DATA
plus numeric proof cost is115.269s (plus4.391s one-time generic decoder setup),
compared with the previously observed133.066s mask proof. These are single-input
observations with existing generic application objects, not an end-to-end cold
speedup, a statistical conclusion, or a best-possible encoding claim.
Calibration additionally needs the26.127s baseline DATA compilation. The actual
module-import audit proves the standalone provider does not import that baseline
DATA or the old accepted133s proof.

All16 compiler attempts are preserved. Fourteen passed. The original256 DATA
attempt failed at Lean's default elaborator recursion limit; the unchanged
representation passed with a local depth option. The first import audit failed
type inference for its diagnostic counter and passed after an explicit Nat type.
Neither failure was an OOM or a counterexample. Accepted theorem axiom reports
contain only the standard Lean axioms; numerical equalities use ordinary kernel
evaluation, never native_decide. See ATTEMPTS.json for exact source, object,
receipt, elapsed-time and per-worker RSS identities. No aggregate peak RAM was
measured. Scratch usage is source/log/receipt storage; large regenerable object
banks are intentionally omitted.

## Source regeneration

From this directory, choose a fresh existing-parent output path:

    python3 reproduce.py --out /tmp/balanced-mask-sources

This deterministically regenerates all8 selected source files and checks their
exact accepted hashes. The generator was executed in normal,-O,-OO modes; all
three produced identical source bytes. The same three modes of this frontend
are recorded in FRONTEND_CONTROLS.json. Source-only regeneration is not a new
Lean verification run.

## Clean application proof replay

Install Lean4.34.0-rc2 and the exact generic dependencies listed in
BUILD_CONTEXT.json (Mathlib commit71a80585ee495fc24472fd0eaffc89d94e4fd8d6).
Relocate compiler, generic dependency paths and generic library paths in a COPY
of that context; preserve compiler SHA and every dependency name/revision.
The packaged tested helper checks actual dependency commits and tracked-source
cleanliness. Then run:

    python3 reproduce.py --out /tmp/balanced-mask-kernel --kernel \
      --context /absolute/relocated-context.json --cpus 0 --host-reserve-gib 8

Use a CPU actually available in the environment. The script rebuilds the entire
15-module selected application source closure into a fresh object bank; only
pinned generic libraries are reused. It compiles exact primitive/original mask
theorem types and audits their actual axioms. The default host reserve is512GiB
for the research host;8GiB is an explicit smaller-host choice and requires
adequate free RAM in addition to the48GiB address-space cap. The full fresh
replay of THIS new packet has not been executed; the original incremental
compiler receipts and exact source-regeneration checks are what is accepted.

Other encodings and every historical source/log can be rebuilt from its exact
attempt snapshot with the packaged compile_lean_context.py, whose historical
commands are retained. The recommended replay does not depend on the previous
accepted mask proof: inputs/accepted-mask-input.lean.txt is read as pinned DATA
by the generator only; it is not imported by the provider.

## Trust and limits

The new work establishes exact Nat DATA identities and a kernel numerical
provider. It introduces no new C model, packed-C execution proof, analytic
assumption or mathematical theorem. Existing source-verified segmented checker
and final consumer integration are separate results. Lean's kernel/core and
pinned generic libraries remain trusted as usual; receipt-generation Python,
compiler/OS/hardware and timing measurements remain ordinary execution evidence.
No full finite ray to1.49e12 or full high-count certificate is established here.

The source closure, exact inputs, historical source versions, compiler context,
all available source snapshots/stdout/stderr/rusage/RUN.json, fixed parameters
and hashes are included. SHA256SUMS.json seals every packet member except itself.
