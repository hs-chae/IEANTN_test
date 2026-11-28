# Actual input loader: source and mathematical model connected

`ExplicitFFTInputLoaderSource.lean` proves the entire actual recursive-C input
loop for both original profiles: 400 Fap coefficients on grid 131072, and 2520 w4
coefficients on grid 16777216. The source/claim identities and the accepted
21-module source-associated replay are in `INPUT_LOADER_MANIFEST.json`.

The theorem constructs actual execution of every source row and proves that
every permitted execution produces the same state. It consumes the actual
`encoded_node` C source output, both absolute-value/sign branches, all temporary
births, scaled integer packing, four physical stores, canonicalization, reflected
12-word copying and the real j increment. The loop covers every original grid
position, including zero padding, and proves that the resulting complex integer
cells are exactly the existing `FFT.IntegerModel.input` and
`FFT.IntegerModel.W4.input` definitions. No input vector or source lookup result
is supplied as an unverified premise. The audit checks every listed source and
mathematical path is consumed, with only the three standard axioms.

The precise caller obligation is an actual typed zero data allocation and real
source locals `data`, `n`, `j=0`. Those must come from the program's own
initialization and reset instructions. They are not trusted platform facts.
The loop restores caller names/scope, proves clock monotonicity, preserves
foreign state and all old objects except the data allocation and the explicitly
updated j cell. Temporary block variables are actually freed.

The independent source syntax proofs for both preserved recursive C files and
the source-main loop locator at statement 21 are included in the final theorem.
All 14 row statements are matched to the actual existing AST; accepted C sources,
coefficients, grids and numerical algorithms remain unchanged.

A clean source-cold replay can be produced with the campaign's pinned compiler,
mathlib/dependency context and the tracked source files:

```
python Solutions/RH080Next.v1/pv/reproduce_lean.py \
  --context /path/to/clean_proof_context.json --run /fresh/owned/input-loader \
  --root ExplicitFFTInputLoaderAudit
```

The recorded run is a source-associated batch, not a fresh source-cold replay
or completed source-first PV of the ANT result. The complete main/FFT/norm/ANT
connection, final combined replay and separate whole-program native receipts
remain separate obligations. The selected restricted-C model/ABI and pinned
compiler/core-runtime/OS/hardware trust boundary are unchanged.
