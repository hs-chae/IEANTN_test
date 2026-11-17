# Reproduce the five-family final verification

This session checks fixed existing height, mass, first-moment, unpaired-300 and
Gaussian-basis source-first proof chains. It changes no numerical algorithm,
parameter, analytic assumption or historical exposure result. The final HTML and
frozen result record distinguish accepted source-first chains from pending
context, network and official-verification obligations.

## Clean reproduction — incomplete final acceptance hook

**This is not yet a complete clean end-to-end replay of this session.** The
source/control snapshot passed input, application and component checks, but its
full default still stops at the final283 typed-index selection. A portable,
parameterized producer → checkpoint → audit → seal hook for the 26 existing
kernel-baseline roots remains unfinished. The actual host audit/readback is
preserved separately; copying its receipt into a new run would not fix this gap.
Do not start the long default expecting final acceptance from this snapshot.
The commands below document source/component replay and its known stopping point.

Download the adjacent pinned source package
`QRH_SOURCE_FIRST_RESEARCH_REPRODUCTION_20261116.tar.xz` and verify:

```text
bytes   44182004
sha256  3c8fde3388dcf09478e7e26c63318f6532421c07a96dfaf7ca90d6ee8c75636d
```

Also download the small `QRH_REPRODUCTION_CONTROL_OVERLAY_20261117_V5.tar.xz`:

```text
bytes   249764
sha256  fea992781a9ae9baa4100030949a277807d3a9cbf61397c6212f807468925c86
```

The original archive is preserved. Its unexecuted master v3 contains a now-known
control-path, wall-limit, partial-import-view and child-stdout readback defects. Apply this checked overlay before running
the current clean recipe; do not run that old default as the corrected route.
In a fresh directory containing both downloaded files:

```sh
tar -xf QRH_SOURCE_FIRST_RESEARCH_REPRODUCTION_20261116.tar.xz
tar -xf QRH_REPRODUCTION_CONTROL_OVERLAY_20261117_V5.tar.xz
python3 -I -B QRH_REPRODUCTION_CONTROL_OVERLAY_20261117_V5/apply_overlay_v5.py \
  --base QRH_SOURCE_FIRST_RESEARCH_REPRODUCTION_20261116 \
  --out REPAIRED_QRH_REPRO
cd REPAIRED_QRH_REPRO
python3 -I -B R/research/complete-clean-reproduction-v1/bootstrap_public_v2.py \
  --packet "$PWD" --out "$PWD/R/work/public-bootstrap"
python3 -I -B R/research/complete-clean-reproduction-v1/reproduce_research_v7.py \
  --packet "$PWD" \
  --environment "$PWD/R/work/public-bootstrap/environment/ENVIRONMENT.json" \
  --check-inputs
```

The archived full-default interface replaces `--check-inputs` with
`--out "$PWD/R/work/full-clean" --jobs 8`. Follow the corrected
`R/research/complete-clean-reproduction-v1/README_CLEAN_RESEARCH.md` inside that
new derived directory. The original extracted packet remains untouched.
The actual tests extracted both published archives, applied the correction and
passed v7 input checks. All 36 new relocated helper/controller controls passed in
normal, `-O` and `-OO` modes. Six actual matching-policy guard CLI controls are
retained as a separately pinned source-identical component. This is not a full numerical/proof rerun.

The commands provision pinned public generic dependencies, regenerate the actual C/C++
numerical workloads and Lean sources, and build the original, research, context
and final-consumer proof chains without distributing an application object bank.
Use the source manifest, not a moving dependency branch. Fixed numerical
workloads use no random seed.

The requirements are Linux amd64, user-systemd, the recorded namespace support
and pinned system development tools. For the full high-resource route, check
genuinely available RAM and free disk separately: each must be at least 1 TiB.
The supplied controller protects host reserves and retains the 300 GiB aggregate
RAM/scratch and 64 CPU policy. Do not launch overlapping full reproductions or
wrap the controller in a small parent memory scope.

The monolithic default is an incomplete end-to-end reproduction route with the
known final283 stopping point above. It has not passed an uninterrupted full run. Actual
component runs and source-built continuations have separately pinned receipts;
the report never converts a recipe into execution evidence. A failed or pending
stage cannot produce final acceptance.

## Inspect this session's evidence

Verify `EVIDENCE.tar.gz` against `Evidence/ARTIFACT_IDENTITIES.json` before
extracting it into a fresh directory. Its internal manifest lists the exact
included paths, byte counts and SHA-256 hashes. Only explicit research sources,
commands, minimal numerical outputs, proof/compiler/source-association receipts
and concise resource evidence are included. Original failed runs remain
historical evidence; later proof completion does not rescore them.

`Evidence/FINAL_REPORT_DATA.json` is the human report's frozen result record.
The family-to-consumer map names the exact written `(file, line, declaration)`
identities and compiler identities. Eight representative ANT consumers help
explain the five-family composition; they do not replace the complete 283-entry
research inventory. That inventory includes source-backed/generic propositions,
intentional kernel-only baselines and one unchanged nonproof datum, rather than
283 independently verified C programs.

The source/AST/execution and same-output consumer proofs are mathematical
acceptance. Native observations, untrusted `#eval` witness proposals, ordinary
certificate checks, kernel-only challengers, public-interface comparators and
official network-verification receipts have different roles. The pinned Lean
kernel, standard axioms, compiler/ABI, generic runtime and documented OS/API/
hardware contracts remain explicit. None of these generic contracts grants
application initialization, successful execution or correct output as an axiom.

## Resume a pending stage

Read the frozen final result and restart notes first. Validate the exact source,
payload, request, compiler and parent receipt pins before reusing an accepted
source-built prefix. Use a fresh output directory; preserve any failed run and
its resource/OOM evidence. A source-built continuation is not a second empty-bank
run. If the report marks a phase pending, its existence in the clean recipe is
not a claim that this session completed it.

All jobs from this capped session have been stopped before publication. Restart
is a new explicit work session; publication starts no background workers.

## Storage

The archive contains no application object bank, giant raw prime arrays,
compilation cache or private conversation/context. The mathematical sources,
locked inputs, minimal native outputs and essential accepted/failed receipts
are retained. Cleanup receipts enumerate any verified-regenerable,
experiment-owned temporary data actually removed. No absence of a cleanup entry
should be interpreted as evidence that a directory was deleted.
