# Reproducing Experiment 1

Read E1_FINAL_REPORT.html first for the rendered mathematical statements, then E1_COMPARISON.csv and E1_PHASE4_ADVERSARIAL_NOPV.md for exact domains and the complete baseline functions. This is a retrospective study, not a preregistered comparison. It uses one researcher for N/V/E/Nplus; independent final readers audit the finished research only.

## Source layout and immutable checkpoints

`network/` is the isolated mathematical checkout at historical base00128bef2f361e9f56795ddd4bb0cf0753643b81 plus new solution-local sources. The2080 base files are byte-preserved. Its Git metadata is not part of the downloadable source carrier. Mathematical additions include E1FrozenN.v1, E1NPlus.v1, E1Evolved.v1, E1Comparison.v1 and the evolved supporting solution families. No core statements, fingerprints, official receipts, registry or evidence policy were changed. No official dispatch, push or PR was performed.

The N/V/E checkpoint archives are immutable historical snapshots. Do not overlay them blindly on the final source. Their hashes and the Nplus archive hash are recorded in evidence/checkpoints. Earlier reports state what was then known; the final report gives the completed comparison. Public upstream and owner branch were checked at setup, but the historical base is not called current.

## Two separate Lean environments

Canonical: Lean4.34.0-rc2, Mathlib71a80585ee495fc24472fd0eaffc89d94e4fd8d6.
Actual OpenAI QRH: Lean4.34.1, Mathlibd13f23b723b8a846827a245b89c10fc7d3f11612.
OpenAI source: openai/math7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean.

The core repository lake-manifest pins the canonical Mathlib. The vendored LeanCert source is under Solutions/CH2.v6/LeanCert. Existing solution lakefiles record further dependencies. Compatible OpenAI sources were replayed in a separate environment. Never put canonical objects in the actual environment or vice versa. The one Scalars port changes imports only; numerical programs and mathematical bodies are identical. Actual-body audits verify that the genuine OpenAI theorem is consumed.

## Commands actually run in the original workspace

Working directory:
`/ryu/hyunsik/playground/independence/codex/ivy/ieantn-experiment1-20261106`

The commands below use the recorded warm environments and source-associated caches. Their outputs and exact commands are in the referenced receipts. They are not represented as a tested one-command clean-machine build.

```sh
python3 research/build_nplus.py E1NPlus.Result
python3 research/build_nplus.py E1NPlus.Absolute
python3 research/build_nplus.py E1NPlus.AbsoluteFinal
python3 research/build_nplus.py E1NPlus.TightAll
python3 research/build_nplus.py E1NPlus.Downstream
python3 research/build_nplus.py E1NPlus.WidePrime
python3 research/build_comparison.py E1Comparison.StepLower
python3 research/build_comparison.py E1Comparison.AllGridFloor
python3 research/build_comparison.py E1Comparison.Strict
python3 research/build_comparison.py E1Comparison.Cumulative
python3 research/build_comparison.py E1Comparison.Matched
python3 research/build_actual_nplus.py
python3 research/build_actual_final.py
python3 research/finish_actual.py
python3 research/finish_matched_actual.py
python3 research/audit_final.py
python3 research/audit_final.py actual
python3 research/associate_final.py
```

Use the import order in the recorded build receipts for the16 prime-proof modules before Result. The drivers refuse current owned imports without an associated successful source/object receipt. Each mathematical module build has a300-second bound and explicit memory limit. A failed build never exports a new successful object. Same-pin compatible reuse and freshly compiled modules are recorded separately. Some old expensive native certificates are intentionally reused: the fixed spectral proof historically took6571seconds, and repeating it was not necessary to prove a different mathematical result. The floor box certificate is also reuse; its duplicate300-second run did not pass.

The actual-full driver first failed on a partially populated namespace prefix. `finish_actual.py` checks exact source/object hashes before copying the missing same-pin objects, then replays the actual consumers. It does not alter mathematics or loosen a gate. Use the final source/object association receipt rather than assuming the last driver invocation rebuilt every dependency.

## Moving to a clean machine

The archive contains the full mathematical source and receipt/manifest evidence, not the multi-gigabyte binary object caches. Install each pinned toolchain and fetch its exact Mathlib dependencies separately. Build the existing core and solution libraries using their lakefiles. The new solution-local sources are compiled with the pinned Lean binary, their project directory as `--root`, and `LEAN_PATH` containing the matching library objects. The recorded ENV files contain original absolute paths; relocate these deliberately after verifying library source/pin identities. A full clean-cache replay was not performed here and may take hours, especially native numerical certificates. A byte-manifest check is not a replacement for that Lean replay.

The two public source pins can be retrieved without making any change to this owner's branch. The source carrier preserves the historical private/local base even if a public Git service cannot fetch that commit. It contains neither Git metadata nor private agent context, credentials or transcripts.

## Evidence and trust

`evidence/NPlus/FINAL_ASSOCIATION.json` checks current source/object/receipt bindings, all2080 original files and immutable prior archives. `CANONICAL_FINAL_AUDIT.json` and `ACTUAL_FINAL_AUDIT.json` name the actual claimed roots, transitive axioms, unpruned project-body closures and frozen native-owner source identities. Their raw records preserve root types, binder-use checks, actual OAI consumption and all eight density-source projections. Mathlib internals are not recursively expanded by the project-body traversal; Lean's axiom collector is transitive.

Final matched consumers have67 native facts, including three comparison-certificate facts. Cumulative bound consumers alone have64. The standalone selected D consumers have21. Nplus full paired/pi consumers have51, the prime consumer48 and the inherited Ramanujan propagation61. These counts refer to different exact roots; do not interchange them. OpenAI's QRH and the new generic analytic lemmas use only the standard three axioms. The full estimates remain native-assisted and conditional on the displayed analytic sources.

Fresh method controls total530: V180+110 and E190+50, each across regular Python, -O, -OO, PYTHONOPTIMIZE=1 and PYTHONOPTIMIZE=2. Historical C/D155main+15pure=170 controls are explicitly reused. Numerical acceptance requires a passed result AND the existing lean-verified-program method. Existing checkers and semantics were unchanged. The final archive validator also uses explicit errors and strict JSON, with actual CLI positive/negative tests in all five modes.

The offline HTML embeds its math font and uses no JavaScript, extension or CDN. Its desktop/mobile screenshots and rendering receipts are under evidence/NPlus/browser. Local source links work when the source archive is extracted. Earlier failed drafts and interrupted jobs remain in the immutable research evidence; none is reported as a successful proof.
