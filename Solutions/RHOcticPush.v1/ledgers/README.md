# Research statements, attempts and proof evidence

Start with `EXECUTIVE_THEOREMS.json` or its CSV export. Each leading result has
an exact written Lean identity, physical line, source hash, full argument range,
premise list, mathematical mechanism, consumer and comparison limitation. This
is an explicitly selected executive index, not a census of all source claims
in IEANTN.

`RESEARCH_LEDGER.json` groups the completed mathematical results and the still
incomplete finite-count chain. Its source and execution receipts are separate:
a result can have a checked conditional mathematical proof while a new clean
reproduction or an external workflow remains unfinished. Historical versions
are preserved under `history/`.

`SERIOUS_ATTEMPT_CATALOG.json` enumerates 39 mathematical research routes. It
includes retained predecessors, unsuccessful analytic methods, changes to
numerical proof organization, exact new mathematical bounds and real downstream
consumers. It records why a rejected route was insufficient or invalid. Routine
Lean elaboration failures, dependency setup incidents and validator repairs are
not counted as new mathematical research routes; their original detailed logs
remain in each component's attempt records.

The inventory includes the mandatory octic, Box/Mellin, Ramanujan, signed
spectral, finite-source and network tasks. Its selection was made by the
research coordinator from those actual component records. It does not use a
historical sorry list or a `source_facing` heuristic. It does not claim that all
externally attributed declarations in the entire repository have been audited.

To reproduce the catalog exports and verify every pinned source file:

```sh
python3 Solutions/RHOcticPush.v1/ledgers/build_attempts.py --out /tmp/rh-attempts-fresh
```

Use a fresh output path. This command reproduces JSON/CSV documentation and
checks source hashes; it does not accept a mathematical proof. Actual numerical
and theorem acceptance is supplied by the separately compiled Lean consumers,
their source/object/log identities, axiom and proof-value audits, and the
component reproduction pipelines.

`build_executive.py` regenerates the leading JSON/CSV index from the current
research ledger and actual written declarations. `build_network_graph.py`
enumerates every current canonical metadata node and declared conclusion edge,
checks old mathematical node statements against the pinned baseline, and emits
the complete inventory plus explicitly selected diagrams. Metadata counts do
not establish proof completion or source-provenance coverage. The actual
canonical proof bodies and theorem types have separate Lean audits.

The human-readable English and Korean HTML reports render every displayed
formula statically and state the source packages and unresolved trust
boundaries. Numerical certificate checking is distinguished from source-first
program verification. New coordinator discoveries are not retroactively
attributed to the original independent exposure arms.
