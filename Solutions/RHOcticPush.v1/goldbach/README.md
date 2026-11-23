# Actual sorted ternary Goldbach multiplicity

This is an additive mathematical propagation experiment. Original binary and
ternary nodes, numerical computations and published claims remain unchanged.
`PLAN.json` records the objective before implementation. The historical
`SOURCE_FREEZE.json` pins the first two sources; `FINAL_SOURCE_FREEZE.json` pins
the later consumer with the actual numerical gate discharged.

`sortedTriples n` is the finite set of prime triples `(a,b,p)` with a≤b≤p and
a+b+p=n. Repeated primes are allowed. Exact finite membership is proved.
The generic source assumes existing `IEANTN.GoldbachEvenUpTo H`. For odd n,
each prime p>n/2 with p+4≤n and n−p≤H yields a sorted pair representing the
residual; p is largest. Distinct p give distinct triples by their final
coordinate. The finite injection and cardinality inequality are proved in Lean.

The real-window theorem discharges parity, natural subtraction, sorting and
range obligations from u≥2, n/2<u, v≤n−4 and n−u≤H. Its actual strict finite
prime set excludes both endpoints. No abstract population replaces the triples.

## Completed analytic consumers

`GoldbachFinalSourceConsumer.lean` consumes actual no-argument kernel-verified
M0≤5.72 and M1≤4.6. It has no numerical-moment parameters. Both the full-real-C
count and stronger concrete widths are connected to the actual octic explicit
formula and the complete infinite-zero transport.

The strongest consumer is `RHOcticPush.OptimizedFinal.triples_above_n_minus_H`
in `../octic/OcticOptimizedCertified.lean`. Put u=(n:ℝ)−H. Its explicit hypotheses
are:

* Odd n and2H<n;
* u≥exp24 and2.14891875√u logu≤H−4;
* the finite binary verification `IEANTN.GoldbachEvenUpTo H`;
* RH and the exact general Green/Nicolas/BPT-off-ordinate source hypotheses.

It proves `#sortedTriples n > (1+4.2/logu)√u`. The actual stronger Fourier caps
M0≤5.7184 and M1≤4.576 are proved and consumed; **no numerical premises remain**.
The previously proved width2.1492 and fixed2.15 count with leading5629/5625 remain
preserved in the earlier final source. No new numerical Goldbach provider is
introduced.

This is a representation-count consequence. It proves neither binary Goldbach
nor a global ternary-existence record. Finite binary verification, geometry and
general analytic literature inputs remain visible. It is ordinary mathematical
Lean/kernel verification, not source-first PV. Compiler/runtime/hardware are
trusted; no native execution axiom appears in the printed final root audits.

## Reproduction and evidence

Use pinned Lean4.34.0-rc2 and Mathlib
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. The three accepted development
compilations use64GiB address-space caps and two threads; exact source hashes,
commands, lookup banks and GNUtime logs are retained under `evidence/`.
Their nine printed root closures use only propext, Classical.choice and Quot.sound.
Final fresh whole-source replay is a distinct integration gate.

From the network root:

```sh
python3 Solutions/RHOcticPush.v1/integration/reproduce.py --out /data/FRESH_OWNED_RUN
```

The current checked capture must include all three new sources, optimized octic
consumer, complete endpoint proof and unchanged actual
`IEANTN/Vocabulary/Goldbach.lean`. An older capture or developer object does not
establish this fresh gate. See the integration report for its actual status.

The initially missing core Goldbach module was compiled unchanged into owned
`/data/ivy-rh-octic-20261123/goldbach-core-v1/objects`. A193-file symlink lookup
union was created inside owned scratch because Lean resolves an entire module
prefix from its first bank. These are development aids; accepted baseline banks
were never modified. Failed import/projection attempts remain documented in
`../octic/ATTEMPTS.md`. There were no numerical jobs, generated bulk data or OOM
events in this combinatorial scope. Accepted proof artifacts are preserved.
