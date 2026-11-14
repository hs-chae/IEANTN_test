# Scoped Winner source-first PV: partial research checkpoint

**IN PROGRESS. This checkpoint does not complete the requested migration.**
The existing Scoped Winner final theorem still has its original 49 native
execution dependencies; the joint before/after comparison consumes 50 in their
union. The comparison-only theorem has zero. No official network evidence or
mathematical assumptions are changed here.

The immutable target is the original 39 comparator identities, 8,192 versus
16,384 integration cells, coefficients 0.009474458010474448 and
0.009471462010471452, and strict comparison for exp(330) ≤ x ≤ exp(331).
See the frozen identity and written-owner registries in `evidence/`.

Completed partial work in this checkpoint:

* Actual handwritten C++ evaluators reproduce all 52 rows underlying the 50
  joint numerical facts. They use the pinned generic Lean Nat object ABI,
  rather than calling a Lean evaluator or embedding computed answers.
* The 734-file C++ include bundle is associated compositionally with the full
  structured source AST. Lean proves every leaf binding, include-tree assembly,
  and exact functions/types/globals/input-array projections. The compiler and
  preprocessor remain explicitly trusted generic tools.
* The operational model includes checked C integers, records, pointers, arrays,
  explicit initialization and logical ownership. Source-body proofs currently
  cover comparisons and pool registration/clearing, including retained values.
* Separate mathematical support proves Taylor/logarithm and
  prime-rich interval lemmas. The new fixed-point `basis_fp128.cpp` reproduces
  useful candidate quadratures; it is **not yet source verified**. The proved
  real interval model of its exponential routine is mathematical support only.

Still required: the remaining rational/interval/Taylor/DAG/quadrature C bodies;
complete numerical kernel certificates for the ten grid facts; unchanged Lean
consumer integration; separate final/comparison dependency audits; and a final
isolated source-cold verification. The analytic candidate near 0.00845 and
prospective exposure study are unfinished. Do not cite them as verified results.

`src/Checkpoint.lean` imports the accepted partial checkpoints. Its development
build and selected root axiom audits passed with only propext, Classical.choice
and Quot.sound. This used pinned development dependencies and is not a clean
final source-cold acceptance run. `MANIFEST.json` records exact source identities.
`STATUS.json` and `evidence/` keep numerical runs separate from formal proofs.

## Reproduction

Use Linux x86-64, Lean 4.34.0-rc2, Mathlib commit
71a80585ee495fc24472fd0eaffc89d94e4fd8d6, and the exact checkout containing
this directory. No numerical randomness is used.

```
python3 reproduce.py --check-local
python3 reproduce.py --lean-prefix /path/to/lean-4.34.0-rc2-linux --run-numerics --out /fresh/output
python3 reproduce.py --build-lean --out /another/fresh/output
```

The numerical command builds and executes the actual included program, checks
all 52 source-input bounds with exact rational arithmetic, and separately runs
the new basis scout. The Lean command asks Lake to resolve the existing pinned
path dependencies and build this partial checkpoint. Network access may be
needed for dependency/cache downloads. A full clean Lake reproduction is
**not yet executed for this checkpoint**; the saved development compile is
recorded accurately in `evidence/`. No final migration acceptance is implied.

The executable's generic Nat arithmetic, reference-count operations, Lean
initialization, precise compiler/ABI/runtime, standard I/O and hardware contracts
remain trusted. Application pool initialization, references, buffers and loops
must be proved applicable; output values or successful application execution
are never assumed platform facts. The new 512-bit backend has its own pending
source, overflow, buffer and whole-loop obligations.

The baseline source is commit 9f108629f0039584250b5e5d781f5313bb3d0ea8.
This is supplemental research, not a revision of locked historical outcomes.
