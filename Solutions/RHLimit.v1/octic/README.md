# Octic contracts and actual prime counts

This directory adds ordinary Lean kernel proofs to the pinned RH continuation.
It preserves the historical sources and numerical outcomes. These proofs are
**not source-first program verification (PV)**: no executable numerical source,
source-to-AST correspondence, or new numerical execution claim is made here.

The original six octic contracts in `EvenKernel.lean` are now reduced to two:

| Contract | Status in this directory |
|---|---|
| ScalarGeometry | Proved for every real C in [1.03,16], including fixed2.15 |
| ForwardCoverage | Proved on the entire real ray u≥exp24 |
| PrimePowerCost | Proved for every kernel degree; .058 uniformC, .0155 fixed2.15 |
| TrivialCost | Proved for every kernel degree; bound.001 uniformC |
| ExplicitFormula | Explicit remaining analytic input |
| ZeroEstimate | Explicit remaining analytic input |

`OcticTwoInputs.prime_count_215` and `prime_count_family` retain the original
ordinary prime-count-difference conclusions, with RH and exactly the two
remaining analytic contracts. `OcticStrict.count_215` and `count_family` retain
the stronger count in the interval with **both endpoints strictly excluded**.
No RH-only Lean theorem, global best-known result, or optimality claim is made.
The exact original coefficients, thresholds and bonus terms are unchanged.

The finite prime-power proof actually reindexes the original Mangoldt sum into
prime powers using Mathlib's Chebyshev identity. It isolates exponent1 as the
original prime population, pays the factor1/k in log(p^k), and bounds each actual
root window by its length plus1. Harmonic and reciprocal-square tails then
produce an analytic envelope. Elementary exponential and logarithmic estimates
prove that envelope below the original constants. It does not check a list of
hardcoded primes or infer a number from an unchecked output file.

## Reproduce from source

Use the exact repository revision containing this directory. Install the pinned
Lean4.34.0-rc2 compiler and Mathlib revision71a80585ee495fc24472fd0eaffc89d94e4fd8d6
with the other generic dependencies recorded in
`Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json`. The compiler SHA256 is
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
For a relocated checkout, set `IEANTN_GENERIC_CONTEXT` to a JSON copy with local
compiler/dependency/library paths updated; retain every dependency revision and
the compiler hash. Generic dependency tracked sources must be clean. Generic
Mathlib/Lean proof libraries may be reused; application proof objects are rebuilt.

From the `network` directory, run:

```
python Solutions/RHLimit.v1/octic/reproduce.py --out /absolute/fresh/output --check
python Solutions/RHLimit.v1/octic/reproduce.py --out /absolute/fresh/output
```

The second command rebuilds the111 frozen historical application modules and
the selected new modules in a fresh directory. Its `LEAN_PATH` contains only
that new object directory and the pinned generic libraries. It never imports an
old application proof object. Exact source and object hashes, compiler commands,
per-module GNU-time wall time and peak RSS, and the final theorem axiom audits
are recorded in `BUILD.json`, `RESULT.json`, `source/`, `objects/`, and `logs/`.
A module is accepted only after a successful compiler return and exact audit
identity matching; only propext, Classical.choice and Quot.sound are permitted.
The complete graph replay needs several minutes. It uses at most80GiB virtual
address space per Lean process and8 Lean threads, with actual use reported
separately. No random seed or numerical dataset is involved.

`compile.py` is the separate incremental **development** runner. It checks a
historical source/object bank and may reuse its objects; its receipt explicitly
says that it is not a clean whole-graph replay. Do not substitute that receipt
for the full source replay.

The seventh strict-endpoint module was added after the initial six-module
source freeze. The recorded first verification therefore uses a completed
117-source replay followed by `append_strict.py --base-run /path/to/cold117
--out /absolute/fresh/strict`, checking every source/object association and
rebuilding the strict consumer against that same fresh bank. The receipt labels
this two-stage118-source chain explicitly. It is not presented as a second
independent cold118 run.

Run parser/audit negative tests in all Python optimization modes:

```
python Solutions/RHLimit.v1/octic/reproduce.py --out /absolute/unused --self-test
python -O Solutions/RHLimit.v1/octic/reproduce.py --out /absolute/unused --self-test
python -OO Solutions/RHLimit.v1/octic/reproduce.py --out /absolute/unused --self-test
```

No acceptance check depends on Python assert or __debug__. Duplicate JSON keys,
nonfinite/overflowing JSON values, unexpected declaration identities, and
nonstandard axioms are rejected explicitly. A failed compiler run retains its
source and logs without publishing a successful final receipt.

## Trust and source scope

The mathematical proofs rely on Lean's kernel, its standard logical axioms,
the pinned generic proof libraries, and faithful compiler/runtime/hardware
execution. The remaining EF and zero-estimate contracts are actual hypotheses,
not kernel axioms or proved consequences of RH. This work does not discharge
their published analytic inputs, Fourier moment caps, or infinite zero-series
limits. No native execution axiom appears in the audited final roots.

There is no new numerical-source or C-program trust boundary in these four
proof closures. The historical octic numerical certificate retains its original
tier and is not consumed as a proved replacement for the zero-estimate input.
The named source for the finite BPT bridge is JNT238(2022), Corollary1,p743;
`ANALYTIC_INDEPENDENT_REVIEW.json` records a separate finite-interface review.
The exact local formulas and original claimed targets are in historical
`parabolic/EvenKernel.lean`, `OcticConsumer.lean` and `OCTIC_PROOF.md`.

`PROGRESS.json` inventories exact(file,declaration,line) identities and accepted
incremental receipts. `HANDOFF.md` records the current source-replay completion
and remaining work. Failed development runs remain under the experiment-owned
`/data/ivy-rh-limit-20261122/octic`; none is counted as an accepted theorem.
No large prime lists, certificates, numerical arrays or caches were generated.
Accepted proof objects, original sources and source-reproduction receipts are
preserved. Any later cleanup must preview only this experiment's regenerable
temporary outputs and preserve accepted artifacts and the only evidence copy.
