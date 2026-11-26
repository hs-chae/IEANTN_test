# Additive canonical evolution of the original finite Fap results

Three new node versions connect completed proofs to the existing network:

| New node | Statement and proof |
|---|---|
| `CMSZeroSummation.v1` | The exact existing general weighted-zero rule, now proved by the Lean kernel without an imported generalized proof-scheme premise. |
| `FapFourierNorm.v2` | The unchanged original Fap norm cap, proved from the complete actual modeled C main/printf execution and its verified numerical output. |
| `RHFiniteAffineIntervals.v2` | The same four original finite prime-interval conclusions, importing the new supporting zero and norm nodes. |

The original norm is 0.7817960157900848. The original strict real prime intervals retain coefficient 0.8 on 4 ≤ x ≤ exp(174), 0.74 on 11 ≤ x ≤ exp(63), and 0.75 on 11 ≤ x ≤ exp(70). The elementary 0.777 branch on 4 ≤ x < 11 has no mathematical input assumption. The exact original 400 coefficients, mesh 80, 131072-point FFT, 17 stages and integer arithmetic are preserved. The v2 table aliases the old data instead of duplicating it.

The six generated Challenge interfaces compile in environments separate from the three actual Solution entry points. Their permanent Challenge stubs remain deliberately admitted; the Solution proofs use only the three standard axioms. Three further composed theorems supply the proved zero and source norm nodes themselves, so their signatures contain neither an assumed numerical norm nor an unproved generalized zero rule. All nine audited proof roots consume the expected actual mathematical/source paths, including the complete operational main, all-call correctness, printed arguments and returned-output equality.

The eight named analytic/historical source propositions plus ordinary RH remain explicit mathematical inputs. This completion does not pretend to have proved their published proofs in Lean. Compiler/runtime, restricted C/typed-memory/LP64/uint64 semantics, generic allocation and stdio/physical-flush contracts, OS and hardware remain documented trust boundaries. Allocation or I/O failure is not assumed away in the universal application-source theorem.

`CANONICAL_EVOLUTION_MANIFEST.json` lists every new node/Solution/helper file and hash. It records 16 fresh proof sources over 666 validated dependencies, 163.96 seconds, maximum Lean process RSS 5684156 KiB and no OOM event. This is a source-associated replay, not a claim that all 682 modules were freshly compiled in that run. The complete fresh operational-main replay is separately recorded by the parent campaign.

The actual local validator passed under normal Python, `-O` and `-OO`, each time compiling all six Solution/Challenge entry-point routes. Normal repository CLI fingerprint generation/check, graph/closure/pin checks and generated-Challenge checks also passed. All 23 preserved original v1 files remain byte-identical. Metadata remains `awaiting-verification` with a local `lean-noncompliant` justification; no official Comparator or workflow receipt is manufactured.

## Reproduce

Use the exact toolchain and eight generic dependencies in `pv/DEPENDENCIES.json`, creating a clean generic-only context with `pv/make_context.py`. Regenerate the unchanged N17 numerical forest and the full operational-main source proof base through the campaign's existing numerical and source-cold reproduction pipelines. The base is a regenerated dependency, not an unverified numerical premise. The public `primal/reproduce_fap_fft_math.py` and `pv/reproduce_main_source_cold.py` retain the fixed original algorithms, exact input and proof sources; the main campaign README describes the complete ordering.

Then select fresh absolute paths `CONTEXT`, `SOURCE_BANK`, `RUN` and `GATE`:

```sh
python Solutions/RH080Next.v1/explicit/reproduce_canonical_evolution.py \
  --context "$CONTEXT" --bank "$SOURCE_BANK" \
  --root CanonicalEvolutionAudit --run "$RUN" --memory-gib 128
python Solutions/RH080Next.v1/explicit/verify_canonical_evolution.py \
  --context "$CONTEXT" --bank "$RUN" \
  --baseline Solutions/RH080Next.v1/explicit/CANONICAL_EVOLUTION_BASELINE.json \
  --out "$GATE"
```

The compiler reuses only source/hash/receipt-associated dependencies and resolves new canonical files from the actual checkout. The strict gate revalidates every actual dependency and compiler route, the complete import closure, nine root audits, six exact interfaces, original data/statements, Comparator theorem selection and the preserved v1 baseline. Repeat it with `python -O` and `python -OO`, using fresh output paths.

For the normal canonical checks, install the pinned CLI packages from the campaign dependency record, use the exact root toolchain and run:

```sh
lake --no-cache build ieantn_hash
python scripts/ieantn.py fingerprint --check
python scripts/ieantn.py check-graph
python scripts/ieantn.py check-closure
python scripts/ieantn.py check-pins
python scripts/ieantn.py gen-challenges --check
```

The three Solution Lake projects require the existing `RH080Next.v1` project. `CANONICAL_EVOLUTION_LAKE_BLOCK.toml` is the additive list of reviewed mathematical/helper roots for the parent to merge alongside the already verified source-program roots. This lane does not edit that shared Lake configuration. Individual actual Solution and Challenge compilation is recorded independently of an official Comparator run.

W4/N24 completion, its future canonical nodes and the whole-network report remain separate stages. No original experimental outcome, optimality claim or causal advantage for PV is changed by this node registration.
