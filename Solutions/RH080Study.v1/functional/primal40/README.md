# Exact degree80 Gaussian witness

This folder certifies the frozen 41-coefficient Laguerre input in
`CANDIDATE_LAGUERRE40.json` (Laguerre degree40, physical degree80). The actual
functions are `G40Functions.physicalF/G`: evaluate the exact polynomials at
√π x and multiply by exp(−π x²). Fourier convention is exp(−2π i x t).
The candidate and all physical coefficients are unchanged from the predecessor
search input SHA dbe388a3208a982e9d9f725f2bac16071ac4ddacb45c7d0cac548a6db6884da9.

All 1,193 finite cell proofs and their two complete aggregation proofs were
actually accepted by the Lean kernel. The full infinite-ray, rescaling and
exterior-wing proofs then establish mass≤0.74901918, exterior positive
Fourier leakage≤0.03111791 and F(0)≥0.999999999. At A=36/11 their denominator
is at least9879755229/11000000000; the inverse quotient is at most
2746403660/3293251743, strictly below0.833948898. These are kernel-only
numerical proofs, **not source-first PV**. There is no native execution axiom.
The exact accepted type/source/object receipts are in `evidence/` and
`VERIFIED_NUMERICAL_RESULTS.json`. A separate final cold replay and final
ANT consumers are recorded by the sibling `primal80_gap` lane; do not infer
its completion from a cell-generation receipt.

`G40Tail/G40Rays` cover the complete infinite tail; no finite-cutoff premise
is imported. Finite intervals reach12 and use Taylor degree8, exponential
Taylor order24, 256-bit upward rounding and 80-bit upward cell rounding. Endpoints
and all arithmetic are rational. `PARTITION.json` is the exact fixed partition
(600 norm cells,593 positive-wing cells); no randomness is used. The 25 source
chunks have exact hashes in `CELL_SOURCE_MANIFEST.json` and are generated
proof inputs, not trusted numerical outputs. Each cell validity proposition
is checked using `decide +kernel`, and its integral bound follows from the
proved generic checker. The standard logical axioms are propext,
Classical.choice and Quot.sound.

## Reproduce from source

Install the repository-pinned Lean4.34.0-rc2/Mathlib and its pinned LeanCert
source dependencies, following the root reproduction README. Python 3.11.14 (the executed regeneration environment)
with its standard library is sufficient for deterministic certificate generation.
There are no Python numerical packages or random seeds in this generator.
Use a fresh scratch directory outside this checkout:

```sh
python3 Solutions/RH080Study.v1/functional/primal40/regenerate.py \
  --out /absolute/fresh/scratch/degree80-generation
```

This reconstructs the actual P/Q input and all 25 cell sources, verifies every
byte against the frozen manifest/current source, and writes a fresh atomic
`REGENERATION_RECEIPT.json`. It is a source-regeneration receipt, not Lean
acceptance. The same full route is checked under Python normal/-O/-OO modes.
Only after successful regeneration and source/hash verification may its
experiment-owned `raw/` and `source/` directories be removed; preserve the
receipt and the published proof sources. They contain no irreplaceable data.

Compile the **entire** new numerical, true-Fourier and v2 ANT consumer source
cone from the repository root, with a generic dependency context containing
only the pinned compiler and Mathlib dependency paths:

```sh
python3 -OO Solutions/RH080Study.v1/primal80_gap/reproduce_joint.py \
  --context /absolute/checked_generic_context.json \
  --lean-cert-source /absolute/pinned/source/root/containing/LeanCert \
  --out /absolute/fresh/scratch/degree80-joint --workers 8 --worker-memory-gib 32
python3 -OO Solutions/RH080Study.v1/primal80_gap/test_joint_controls.py \
  --accepted /absolute/fresh/scratch/degree80-joint \
  --out /absolute/fresh/scratch/degree80-controls
```

The default route rechecks every new cell and imported generic source; it does
not reuse predecessor numerical leaves. Do not use its optional development
reuse flags for the final cold acceptance run. See `primal80_gap/README.md`
for resource admission and receipt fields. The resource policy preserves a
256GiB available-host reserve and independently checks RAM and free disk.

`prototype_cells.py` explores a different partition; changing its parameters
produces a new candidate verification job. The reproducible accepted route
always uses the frozen `PARTITION.json`. The Python generation algorithms,
OS, compiler and hardware are external execution infrastructure; their
correctness is not a premise of the Lean mathematical proof, because the
kernel independently checks every produced proof input.

The true Fourier proof is in `primal80_fourier/Primal80ActualFourier.lean`.
The RH prime-gap/population applications use unchanged general CMS analytic
source predicates and ordinary RH, explicitly supplied to the final consumers.
The result is asymptotic with every positive epsilon and no explicit onset.
No 0.8 conclusion, global record or optimality claim is made. The compact-dual
C-source-first obstruction elsewhere in this study is a separate result.
