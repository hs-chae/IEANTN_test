# Reproduce the Gaussian mathematical result

Use the complete pinned research checkout. Its `lean-toolchain` pins Lean4.34.0-rc2 and `lake-manifest.json` pins Mathlib71a80585ee495fc24472fd0eaffc89d94e4fd8d6 and its generic dependencies. Restore that toolchain and generic library cache using the campaign's clean-environment bootstrap. Application proof objects are not prerequisites. Source coefficient lists, numerical certificates and analytic tail proofs are ordinary tracked Lean source.

From the repository root:

```sh
python3 Solutions/RHOnePrimeEvolution.v1/gaussian_gap/reproduce.py \
  --repository "$PWD" --run /absolute/fresh/gaussian-proof --jobs 2
```

The frontend chooses the repository's standard `.lake/packages` generic libraries when present, otherwise the exact recorded local context. It checks the compiler version and each generic package's commit and clean tracked source. On a relocated clean machine, `--compiler` and `--generic-lean-path` can explicitly locate those same pinned dependencies. A generic library is `<package>/.lake/build/lib/lean`; the version checks reject application directories masquerading as generic inputs.

The script freezes the source builder and dependency manifests, captures every selected application source before compiling it, and starts with a fresh application object directory. It rebuilds the full norm/positive-wing certificate pipeline, all564cell checks, analytic tails, real scaling, the actual polynomial-Gaussian Fourier transform, all regularity conditions, the general CMS adapters and actual canonical Solution imports. The final audit checks six canonical theorem types, eleven transitive axiom roots, twelve actual provider edges, and actual numerical/source parameter use.

It then checks every source/current-source/object/compiler/log hash and executes six genuine rejection controls. One increments an exact rational Fourier coefficient in a copy of the actual source and must fail the existing kernel arithmetic identity. The others reject a changed gap coefficient, omitted analytic source, omitted numerical witness, an invented explicit onset and removal of the positive population-width epsilon. Those latter controls pin the actual interfaces; they do not assert logical independence of hypotheses or mathematical impossibility of proving stronger bounds by another method.

Acceptance uses explicit checks in Python normal, `-O`, and `-OO` modes, and only publishes a fresh receipt after every check. Final publication uses an exclusive temporary file, flush/fsync, atomic replace and directory fsync. No Python assertion is used for acceptance.

The accepted local full run is recorded in `HANDOFF.json`, with exact source/build/acceptance hashes and independent source review links. Original failed development trials remain in the private execution evidence. A source-only build is distinguished from development overlays that reused explicit numerical proof banks.

The mathematical source assumptions remain universal CMS functional reductions from arXiv1708.04122v2(1.3),(1.11)–(1.14). Read `SOURCE_LEDGER.html` for exact rendered source statements, normalization and hypotheses. Actual Gaussian Fourier/norm/leakage/value-at-zero data are proved, not assumed. This is not a new formal derivation of the published analytic theorem from RH inside Mathlib, not an explicit-onset prime gap bound, and not source-first program verification.

All generated data are small deterministic proof artifacts. No large prime list, floating-point array or unverified execution output is required. Keep the accepted source certificates, proofs and receipts; private compiler outputs and copied generic caches can be regenerated. Do not delete accepted proof artifacts or shared/original caches. Parent-controlled duplicate-cache cleanup is separate from this reproduction procedure.
