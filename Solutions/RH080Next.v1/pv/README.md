# RH080 numerical source verification

This directory contains actual C programs, source-derived Lean ASTs, independent
syntax proofs, checked execution semantics, numerical enclosure proofs and a
matched kernel-only control. Historical RH080Study files are reused unchanged.
The word **PV** below means source-first program verification.

## Completed new population numerical provider

`population_norm.c` computes an upper enclosure of the periodic absolute norm
for the exact 16-node, mesh-8, support-2 witness in `population_m8_r2.json`.
The coefficient scale is 10^18 and the integration grid has 256 cells. It uses
nine-term fixed-point sine, source-computed Fourier sums and a conservative
second-derivative quadrature allowance. The program computes its answer; its
source contains no precomputed norm or desired final theorem bound.

The compiled answer is `887721072633027910 / 10^18`, or
`0.887721072633027910`. The source itself is SHA-256
`92c5832d3ecfdd08d7c4143ac155e47e61ee9f58700634cf4f04e7cf8fc84b09`.

The proof chain is:

1. `PopulationSource.actual_source_syntax` proves character-level source
   correspondence using the existing independently specified restricted C
   grammar, including grouping/precedence and preprocessing. An untrusted
   Python parser only proposes the AST.
2. `PopulationActual.Execution.actual_norm_program` proves evaluation of the
   actual source-derived C AST, with arithmetic checks and loops, to that
   output. It uses kernel reduction, not `native_decide` or an execution axiom.
   The first complete execution proof took 528.37 seconds and peaked at
   50,081,400 KiB RSS.
3. `PopulationMain.actual_main_shape` proves the actual host harness calls the
   numerical function, and `actual_main_output` composes the closed execution
   proof with the generic decimal-printf specification.
4. `PopulationBounds` proves fixed-point sine folding and truncating split
   multiplication enclosures. `PopulationSamples.actual_grid_enclosure` covers
   every sample. `PopulationNorm.periodic_norm_upper` combines those enclosures
   with the general periodic absolute-value chord theorem.
5. `PopulationSourceFinal.source_output_periodic_norm` consumes an actual
   source-output premise and bounds the integral by that computed output.
   `source_first_periodic_norm` instantiates the proved actual execution.
6. `PopulationNodes.polynomial_identity` identifies the numerical polynomial
   with the actual affine Fourier-window polynomial and proves normalization.

`PopulationTrustAudit.lean` independently checks 13 theorem roots, seven direct
proof-value edges, source-execution consumption and the absence of native or
sorry axioms. All roots use only `propext`, `Classical.choice` and `Quot.sound`.
The mathematical inverse-Fourier norm identity and final ANT consumer are
separate from this unconditional periodic numerical provider. In particular,
`Explicit.SourceBRFourierNormFive` is a named published analytic input, not a
kernel-formalized periodization proof; the explicit lane documents that boundary.

## Matched control

`PopulationControl.kernel_only_periodic_norm` proves **exactly the same**
periodic bound, with the same 16 nodes, scale, grid, sine algorithm and numerical
allowances. Its proof-value closure excludes the C AST, source checker and source
execution roots. Source-first PV adds the source-program correspondence; it does
not cause the mathematical improvement of this witness.

## Original w4 provider: partial migration

`window_scalars.c` preserves all 2,520 stored input coefficients, mesh 360 and
scale 10^16. The mathematical node list has an appended terminal zero, length
2,521. All seven scalar C numerical executions, the independent source syntax
proof and the actual host-main output sequence have compiled without native
axioms or sorry. `WindowModel` gives independent finite mathematical
specifications of F0, positive tail area, component height, first variation,
derivative variation, an upward second-moment bound, and maximum coefficient.

The original 16,777,216-node w4 periodic FFT norm and the 131,072-node
mesh-80/radius-5 finite-slab FFT norm have **not** been converted to source-first
PV. The C implementations here do not verify the original Python source bytes. This new 256-cell population program is an additional useful
provider, not a replacement or a claim that the original FFT migration is done.
`WindowRationalBridge` also proves the actual F0, component height, derivative
variation and upward second-moment bounds for the padded mathematical nodes.
Its source-cold proof took 1,626 seconds and peaked at 65,896,652 KiB RSS.
`WindowSourceFinal.source_first_nodal_boundaries` transports actual C outputs
into those four mathematical quantities. Its compiled audit checks 14 roots,
11 direct proof edges and consumption of all seven source executions; only the
standard three Lean axioms occur. A unified source-cold scalar replay is recorded
separately from these successful individually source-associated builds.

## Reproduce

Use the pinned Lean 4.34.0-rc2 / Mathlib commit
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. The baseline checkout is
`1c668b75e6babcc6c01aee63f1cc401c2d70baed`; new source bytes are independently
hashed in the compile receipts. No random seed is used by these fixed-input
numerical programs. A C11 compiler with a 64-bit `uint64_t` and unsigned long long
is required; the recorded compiler is GCC 11.4.0 on Linux x86-64.

From this directory:

```sh
python3 make_context.py --compiler /toolchain/bin/lean --mathlib /path/mathlib \
  --output /absolute/fresh/clean_proof_context.json
python3 check_regeneration.py
python3 run_native.py --run /absolute/fresh/native-run
python3 -O run_native.py --run /absolute/fresh/native-O-run
python3 -OO run_native.py --run /absolute/fresh/native-OO-run
python3 reproduce_lean.py --context /absolute/clean_proof_context.json \
  --run /absolute/fresh/lean-run \
  --root PopulationSourceFinal --root PopulationControl \
  --root PopulationNodes --root PopulationMutations --root PopulationTrustAudit
```

The context JSON specifies the pinned Lean compiler hash and the eight generic
library object roots; construct it using `make_context.py` after building the exact revisions in
`DEPENDENCIES.json`. If dependencies are siblings rather than nested below
Mathlib, supply `--packages /path/to/packages` to that setup command. No application object fallback is permitted. The Lean script
copies the entire application source closure into the fresh run, compiles it in
dependency order, and retains source hashes, commands, individual compilation
receipts and actual `/usr/bin/time -v` resource records. Development-only
`compile_verified_context.py` may reuse precisely source/hash/receipt-associated
application objects; it is explicitly separate from the source-cold replay.

`run_native.py` compiles O0/O2/O3/UBSan binaries, runs them, strictly parses their
captured outputs and compares with the Lean-proved results. Its receipt alone is
an execution observation, not PV. It also runs three adversarial source changes.
`PopulationMutations` proves that the original source checker rejects each
changed source; the changed programs also produce different numerical outputs.
The validators use explicit failures and remain effective with Python -O/-OO.

## Trust and storage

The formal mathematical numerical enclosure and source-AST execution use Lean's
kernel. The remaining platform boundary is the correctness of the pinned Lean
compiler/kernel infrastructure, C compiler and headers, the documented Linux
ABI, integer instructions, process execution and hardware, plus the generic
successful `%llu\n` formatting contract. Physical source/AST fixture association
is checked by deterministic regeneration, byte comparison and hashes. The
application's numerical initialization, selected execution, arithmetic safety,
loop behavior and result are proved, not generic platform assumptions. Native
stdout is checked explicitly; exit code zero alone does not establish an output.
This verifies the stated restricted scalar fragment, not all of C or C++.

All required data here is small and deterministically regenerable. Reproduction
runs need no large prime lists, FFT arrays or retained intermediate certificates.
Private regeneration directories are automatically removed after byte checks.
Retain accepted proof artifacts, exact inputs and receipts; cleanup must remain
within verified experiment-owned temporary directories. Original research inputs
and historical results must remain unchanged.
