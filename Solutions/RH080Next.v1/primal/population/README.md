# Two source-first population programs

The mathematical output is the eventual ordinary-RH prime-population frontier

`min(0.944247 + 1.163388 alpha, 9/8 + (16/15) alpha)`.

For every fixed nonnegative `alpha`, this coefficient is a `GoodCoefficient`:
there is a positive normalized population margin at all sufficiently large real
`x`, and hence more than `alpha*sqrt(x)` primes in the source half-open interval
`(x, x+c*sqrt(x)*log(x)]`. The threshold is not explicit or uniform in `alpha`.
The readable consequences include `c=2.108` for `alpha=1`, and `c=283/24` for
`alpha=10`. These are two fixed witnesses, not an optimized global frontier.

The exact two input coefficient lists live in
`IEANTN/Nodes/AffineFourierPrograms/v1/Tables.lean`. The first has origin value1;
the second has value `1599999999999999999/1600000000000000000`, which is retained.
`AffineProgramsSolution.lean` proves both lists definitionally equal to the actual
C program models. Each source computes256 trigonometric samples, conservative
sine error and chord allowances. Its answer is computed by the algorithm; it is
not inserted as an answer literal in that algorithm.

`BRFourierInput.v1` records two explicit general literature premises: BR v2
Lemma5's literal finite-mesh norm identity, and the q=1 ordinary-RH specialization
of Proposition6, including its error term. The latter specialization comes from
the paper's principal conductor-one proof, not an implication from RH to GRH.
The positive error tends to zero by a completed Lean proof. The inputs are not
claimed to be analytic theorems proved from RH inside Lean.

`AffineProgramsSolution.lean` consumes source syntax correspondence, actual AST
execution, overflow/sine/quadrature correctness, and the resulting scalar
outputs. Actual Fourier transforms, eligibility, mass at0, leakage, attained
maximum and full ANT consumers are Lean proved under those literature inputs.
`PopulationCanonicalAudit.lean` checks18 typed roots and their standard axioms,
verifies both source-output branches are consumed, and rejects matched-control
shortcuts. Conversely `PopulationMatchedControl.lean` uses the same exact inputs,
arithmetic, numerical caps and generic mathematical consumer, while its value
closure excludes actual source-execution facts. The mathematical result is the
same; this experiment does not show a causal advantage of PV over that control.

The exact scalar minimum is strictly below the previous octic leading width
`(9/8)*(alpha+18203/20000)`. The old theorem has explicit onset `exp(24)`, strict
endpoints, a positive `4.2/log(x)` term, and coefficient range `[1.03,16]`; those
features remain in `PrimeInterval.v4` and are not transferred to these new
asymptotic curves. For alpha0 a separate Gaussian witness gives a smaller width.

From a clean pinned checkout with the generic dependencies in the recorded
context, run:

```sh
python3 Solutions/RH080Next.v1/primal/population/reproduce.py \
  --context /absolute/path/to/clean_proof_context.json \
  --out /absolute/path/to/fresh-owned-run --workers 2 --worker-memory-gib 64
```

The controller validates the pinned compiler/dependency
commits, regenerates both source/AST fixtures in its own scratch, checks source
bytes, builds and runs actual C, and freshly compiles the complete Lean source
closure with no application-object fallback. It records commands, hashes,
execution time, measured per-process peak RSS and sampled aggregate RSS, disk
usage and actual resource failures. A final receipt is created only after every
source and exact dependency/axiom audit passes. No random seed is involved.

The Lean kernel, pinned Mathlib/dependency libraries, compiler/runtime and OS/API
and physical hardware remain trusted at the declared infrastructure boundary.
C compilation is independently reproduced and byte-associated with the checked
source; this does not prove GCC or hardware correctness. No native execution
axiom, new mathematical axiom, or admitted proof is accepted on the final path.
Official Comparator approval is absent; local source-cold receipts are separate.
Generated scratch is regenerable; keep source, accepted proof artifacts, exact
input tables, scripts and essential receipts. Only clean verified owned scratch
after comparing its contents with the accepted manifests.

Accepted combined replay:91 freshly compiled sources,18 audited theorem roots,
474.46 seconds,47.74 GiB largest measured process RSS and91.05 GiB sampled
aggregate RSS, with no SIGKILL or bad_alloc. Exact full metrics and hashes are
in ../evidence/POPULATION_CANONICAL_COLD_RESULT.json. A postcheck verified every
frozen/original proof source and both original C source byte hashes.
