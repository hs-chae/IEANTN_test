# Standalone Gaussian proof packet

The `portable/` directory contains all53 application Lean sources needed for the new Gaussian Fourier/numerical result and its actual canonical mathematical consumers. It includes both canonical Solution imports, the general CMS source interfaces, all numerical proof sources and the final eleven-root/twelve-edge axiom/value/type audit. It does not need the original repository, its739-provider registry, private application proof banks or any application `.olean` files.

Install Lean4.34.0-rc2 and restore the eight pinned generic package libraries recorded in `SOURCE_MANIFEST.json`. Each generic library path must end in `.lake/build/lib/lean`, belong to the named Git package with the exact pinned commit, and have clean tracked source. Standard `.lake/packages/mathlib`, `.lake/packages/aesop` and the other listed package directories satisfy that layout. No generic dependency is fetched or silently updated by this frontend.

Copy the complete `portable/` directory anywhere, then run:

```sh
python3 reproduce.py \
  --compiler /absolute/path/to/pinned/lean \
  --generic-lean-path /absolute/mathlib/.lake/build/lib/lean:/absolute/plausible/.lake/build/lib/lean:... \
  --run /absolute/fresh/proof-run --jobs 2
```

Supply all eight listed generic libraries in the colon-separated path. A source/dependency preflight is available with `--check-only`; its output explicitly says that no proof execution occurred. The full command copies and hashes sources, compiles every application module in fresh storage, checks actual theorem dependencies and mathematical interfaces, then runs all six rejection controls. One changes an exact coefficient in the actual Fourier witness and must fail kernel arithmetic. No source numerical data are regenerated through unverified floating-point runs.

Only the compiler and generic library paths come from the host. The frontend validates those source pins, creates run-owned lookup links, and invokes the exact frozen builder with a53-row local source registry. A tiny audit stub contains only the frozen source ledger. It does not resolve an old research checkout or consume predecessor application objects.

`RESULT.json` is published atomically only after complete proof execution and the independent numerical/source/type/value/axiom audit and controls pass. `compile/EXECUTION.json`, `audit/ACCEPTANCE.json`, exact commands, source/object/log hashes and resource measurements are preserved. The supplied manifest is an unsigned consistency record, not an independent authenticity authority; verify its research-branch commit and independent source review through the main report.

The mathematical conclusion is source-conditional: generic published CMS analytic reductions are explicit B inputs, while actual Gaussian Fourier, mass, positive leakage, value at zero, objective arithmetic and final conditional consumers are Lean proofs with standard axioms only. No source-first PV, explicit onset, optimality or exhaustive best-known claim is made.

The frozen `SOURCE_LEDGER.html` renders every source formula offline. Its relative research-layout links can be followed in the full repository; inside this compact packet inspect `source/IEANTN/Vocabulary/CMSFunctional.lean`, the three new node Conclusions modules and the flat Gaussian source files directly. Its primary paper URLs remain usable.

The actual relocated replay and81 real check-only CLI guard cases are recorded in the main `HANDOFF.json` and receipt archive. Guard cases run under normal Python, `-O` and `-OO`; check-only guards are distinguished from full kernel replay. Experiment-owned disposable copies were previewed, checked and deleted. Accepted source certificates, proof artifacts and original research data are preserved.
