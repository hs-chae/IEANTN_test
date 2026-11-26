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

## Second population profile and actual ANT consumers

`flat_population_norm.c` runs the same 16-node, mesh-8, 256-cell algorithm on
`flat_m8_r2.json`: eight coefficients equal to `533333333333333333/10^18`, then
eight zero coefficients. It computes `1120475208606944546/10^18`. Its exact
normalization is `1599999999999999999/1600000000000000000`, rather than 1.
`FlatPopulationSourceFinal.source_first_periodic_norm` and the separately audited
`FlatPopulationControl` supply the same bound with and without source provenance.
The 44-module source-cold closure passed in 530.75 seconds.

Both numerical profiles are consumed by the actual Fourier and ANT population
frontier/count theorems under `../primal`. The combined canonical replay compiled
91 modules from generic libraries alone, checked the physical C source and exact
input tables, and audited 18 theorem roots and source/control separation. Its
receipt is `primal-runs/population-canonical-cold-v1/RESULT.json` in the campaign
evidence bundle. The source-verified flat profile supplies a genuine new bound
for the population problem; the matched kernel-only profile has the same
mathematical conclusion. The separate analytic source hypotheses remain visible.

## Original fixed-input scalar providers

`window_scalars.c` preserves the original 2,520 stored w4 coefficients, mesh 360
and scale 10^16. Its mathematical nodes append a terminal zero, giving length
2,521 and radius 7. All seven actual scalar C executions, independent source
syntax, and seven-output host-main sequence compile without native or sorry
axioms. `WindowModel` independently specifies F0, positive tail area, component
height, first variation, derivative variation, upward second moment and maximum.
`WindowSourceFinal.source_first_nodal_boundaries` connects source outputs to
actual padded-node F0, H, V1 and second-moment bounds. The unified source-cold
27-module replay passed in 2,756.40 seconds, peaking at 65,894,000 KiB RSS.
`../explicit/ExplicitW4SourceMoment.lean` consumes these source outputs in the
actual signed-log Fourier integral theorem.

`fap_scalars.c` preserves the different original finite-slab witness: 400 stored
coefficients, mesh 80, radius 5. `fap_original.json` retains the original 10^12
scale; `fap_scaled.json` multiplies each integer coefficient by exactly 10,000
and uses scale 10^16. `FapRescaling.lean` proves equality of every rational input
and the padded node list. `FapSourceFinal` provides the same seven-output/four
nodal-boundary interface. Its 28-module source-cold replay passed in 231.24
seconds, peaking at 8,135,536 KiB RSS. Fap is the original finite 0.8-slab
provider; w4 is the original ray/global provider. They are never interchangeable.

The scalar execution models check every addition/multiplication against 2^64,
reject unsigned subtraction underflow and division by zero, and traverse actual
source-derived loops and internal calls. The successful execution proofs include
these guards. These are restricted scalar-C models; this is not a claim of a
verified C compiler or an unrestricted C/C++ semantics.

## Original FFT norm migration remains incomplete

`fft/w4_fft.c` and its separate recursive variant implement the actual full
16,777,216-point norm algorithm with signed fixed-point limbs. `fft/fap_fft.c`
and its recursive variant preserve the original Fap nodes and use 131,072 points.
They are mathematically equivalent C ports, not verification of the original
Python bytes. Actual source-character/AST correspondence has compiled for all
four files. Native observations reproduce suitably small numerical candidates,
but those observations are not proved norm enclosures.

The reused Goldbach C model gives explicit word promotions/wrapping, typed
pointer loads/stores, object identity, scopes/lifetimes and actual own-function
calls. New proofs cover word-array access/store, initialization from byte calloc,
source store statements, digit/overflow bounds, exact input scaling and mass.
`FFTActualRoot` proves the actual C root initializer's complete selected
operational call in a canonical scratch frame, including its limb arithmetic
and helper loops. `FFTDecodedSeed.source_initializer_seed_bound` connects its
12 computed words to the true complex root with error at most 10^(-26).

Generic caller framing, independence of permitted operand orders, full signed
limb/helper-loop contracts, actual twiddle/input/recursive FFT refinement,
fixed full-grid numerical output proofs and original norm consumers remain
open. A proved memory subtrace or one selected initializer call is not the
complete FFT program proof. `evidence/PUBLICATION_MANIFEST.json` separates
accepted scoped proof modules from pending files and lists exact source,
object and receipt hashes. No original numerical outcome is changed.

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
python3 reproduce_lean.py --context /absolute/clean_proof_context.json \
  --run /absolute/fresh/flat-lean-run \
  --root FlatPopulationSourceFinal --root FlatPopulationControl \
  --root FlatPopulationNodes --root FlatPopulationTrustAudit
python3 reproduce_lean.py --context /absolute/clean_proof_context.json \
  --run /absolute/fresh/original-scalars-run \
  --root WindowSourceFinal --root WindowTrustAudit \
  --root FapSourceFinal --root FapTrustAudit --root FapRescaling
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
is checked by deterministic regeneration, byte comparison and hashes. For the completed scalar and population providers, the
application's numerical initialization, selected execution, arithmetic safety,
loop behavior and result are proved, not generic platform assumptions. The
FFT source has only the explicitly enumerated partial obligations completed. Native
stdout is checked explicitly; exit code zero alone does not establish an output.
This verifies the stated restricted scalar fragment, not all of C or C++.

All required data here is small and deterministically regenerable. Reproduction
runs need no large prime lists, FFT arrays or retained intermediate certificates.
Private regeneration directories are automatically removed after byte checks.
Retain accepted proof artifacts, exact inputs and receipts; cleanup must remain
within verified experiment-owned temporary directories. Original research inputs
and historical results must remain unchanged.

### Multiplication row source refinement (partial FFT migration)

`FFTProductBindings`, `FFTProductInner`, and `FFTProductRowLoop` prove the actual `fixed_multiply` AST inner body and complete five-digit row. The proof establishes actual declarations of `k`/`t`, all 64-bit arithmetic and typed stores, preserved input slices (including disjoint slices in one allocation), real block scope exit, arbitrary old caller-object framing, and the integer-valued schoolbook row conservation law. Variable lifetime owners are tracked individually: function parameters and `i` differ from the row-local `j`/`carry`.

The fresh 47-source replay passed in 135.82 seconds, peak child RSS 3,460,260 KiB, no OOM, using only the pinned generic dependency context. Reproduce with `reproduce_lean.py --context <clean_proof_context.json> --root FFTProductRowLoop --run <fresh directory>`. `evidence/FFT_ROW_SOURCE_RESULT.json` records exact source and receipt hashes. This is a restricted actual-AST source proof. The whole `fixed_multiply` function, full recursive FFT source correspondence to the accepted numerical trace, and original numerical ANT norm argument remain incomplete; these row results alone are not a completed source-first PV claim for the FFT.

### Complete multiplication core and real call-entry prefix

`FFTProductCoreAudit` freshly rebuilds 62 source modules, including both actual recursive C source grammar proofs, and checks ten roots with 10,111 dependencies and only the standard three axioms. The accepted run took 1065.37 seconds, peak child RSS 38,875,452 KiB, disk 466,750,974 bytes, no OOM. Every source/snapshot/object/log hash and every compiler diagnostic was checked after completion, including rejection of PANIC/IRPANIC even with a zero process exit code.

The actual nested 25-digit product core has constructive termination and correctness for every permitted execution order. `FFTFixedMultiplyBeginSource` additionally consumes the actual program lookup, real callee scope entry, four pointer parameter declarations, actual `zero_words` call, and real local `i` initialization. It proves the full ten-digit product while preserving all six words of each input, all four parameters, and unrelated caller objects. These additional call-entry proofs were compiled as source-associated extensions; they are not described as another fresh 62-module replay. Reproduce them from clean source using the two commands recorded in `evidence/FFT_MULTIPLICATION_CORE_RESULT.json`.

The sign/drop/output/increment/canonical/return suffix, full helper Call, and whole recursive FFT numerical proof remain open. The canonical selected-state initializer proofs do not establish applicability to main's `root=work+128` shared-allocation layout. That must follow from the generic disjoint-slice helper contracts and the actual main initialization.

### Meaning of completed PV

Owner-defined PV requires the complete connection from actual C/C++/CUDA source, through independent AST correspondence, execution semantics and mathematical correctness, to the actual IEANTN theorem consuming the source-linked output. A completed helper contract proves the source/AST/execution/correctness part for that function; it is not completed PV until the real caller and ANT theorem consume it. Historical receipt flags or filenames containing `PV` do not change that distinction. The original scalar providers are consumed by the explicit conditional `_of_norm` ANT applications; the original FFT numerical norm source chain remains open.
