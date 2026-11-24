# Independent source syntax for the fixed prime counter

This study adds a source-to-AST **surface-syntax soundness theorem** for the
unchanged `verified_quotient_count.c` and the additional high-input C main.
It preserves the existing counter AST, execution semantics, arithmetic proofs,
arrays, input `1490000000000`, and mathematical conclusions. The scope is these
two actual C files and their guarded canonical source fragment. It does not
implement a full ISO-C frontend or migrate every IEANTN numerical program.

## What is proved

`CounterGrammar.lean` independently specifies character-level identifiers,
integer literals, explicitly parenthesized expressions, assignments and lvalues,
array indexing, calls, single declarations, matched conditionals, blocks, while
loops, declaration-initialized for loops, functions, prototypes, positive static
arrays, fixed includes and safe comments. No grammar judgment mentions the
renderer, token lists, acceptance, or an expected execution result.

`CounterRendererSound.checkedCounter_sound` and `checkedDriver_sound` prove
**for every supported AST and source string** that successful strict checking
implies this independently specified grammar relation. The proof is structural
Lean reasoning. Actual finite AST-profile facts use kernel `decide +kernel`.
There is no `native_decide`, new axiom, or `sorry` in these modules.

The original permissive rendered-byte/token predicate is preserved. Its arbitrary
operator, identifier, type, control-body and for-initializer possibilities do not
justify a general C grammar claim. The added checker requires both a supported
AST profile and exact physical source bytes. It intentionally rejects different
spellings, even harmless alternative whitespace. Existing exact-byte proofs are
reused to accept the two unchanged actual programs; general checker soundness
then produces their independent syntax derivations.

`CounterGrammarConsumer.SourceDriverRun` indexes the existing formal main run by
both actual source strings and requires both grammar derivations. The theorem
`complete_canonical_source_run` constructs an inhabited successful source-indexed
run whose committed output is `wordBytes (Nat.primeCounting 1490000000000)`.
The generic grammar soundness and both source-byte proofs are consumed in this
construction. `CounterSyntaxAudit.lean` checks the actual proof-value edges and
root-to-endpoint reachability, separately from the full theorem axiom audit.

The exact value `55206486339` remains a separate numerical gate. The conditional
adapter `source_output_of_exact_count` does not discharge that gate. Once the
immutable exhaustive kernel count finishes, a **new final existential consumer**
must rewrite `complete_canonical_source_run` with that theorem so the fixed-value
result consumes the count and both grammar derivations together. The separate
finite-counter agent owns that final adapter. A conditional successful-run lemma
alone does not supply this inhabited source-run construction.

## Precise boundaries

The target is independent surface syntax with the intended AST structure. It is
not a general name-resolution or C type-correctness theorem. For example, a
lexically valid but undeclared variable can pass the generic surface grammar.
The actual programs' declarations and references were independently inspected;
the preserved application model separately proves initialization and execution
correctness. Generic typing, integer-conversion rules, header expansion and
operational adequacy of that chosen C model are not established by grammar alone.

The comment rule excludes non-ASCII/control spelling, backslashes, question
marks and literal `*/`, preventing hidden terminators formed by C11 trigraphs
or line splicing. The actual fixed copyright was already safe; the early broad
comment rule was repaired before freezing. Fully parenthesized expressions and
matched `if/else` productions handle precedence and dangling-else attachment.
The actual files contain no casts or postfix increments; those AST forms are
rejected by this supported fragment rather than assigned guessed semantics.

The primary syntax reference is the preserved WG14 N1570 C11 committee draft.
`INDEPENDENT_STANDARD_REVIEW.json` identifies exact clauses and PDF pages for
every production family and distinguishes surface syntax from constraints.
There is no separate Blueprint label for this new experiment; its correspondence
is the original `QuotientCSourceV2` AST and the high-driver application contract.
The compiler syntax smoke test is supporting testing, not the soundness proof.

Pinned Lean, generic libraries, compiler/runtime, ABI, headers, stdio, OS, and
hardware remain explicit infrastructure or interpretation contracts. A lifted
model run is not an assertion that a particular physical compiled run succeeded.
These syntax and kernel-model results alone are **not complete source-first PV**.
Source-first PV must also connect the selected compiled execution and verified
numerical output to the actual theorem through the documented contracts.

## Reproduction

Use the pinned Lean `v4.34.0-rc2` compiler (SHA256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`),
Mathlib commit `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`, and other generic
package revisions recorded in `Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json`.
Install these generic dependencies first and build/download their matching
generic library objects. On another machine, supply a context file with its
absolute paths while retaining compiler hash and dependency commits. No prior
application proof object is needed for the clean composed recipe.

From the network root:

```sh
python3 Solutions/RHOcticPush.v1/finite-pv/grammar/reproduce_from_clean.py \
  --out /absolute/fresh/counter-grammar --context /absolute/pinned-context.json
```

That regenerates the complete existing application source closure from the
preserved source pack, builds its 31 scientific modules and audit, builds the
four new modules and new audit, then runs the actual acceptance CLI in normal,
`-O`, and `-OO` modes. The wrapper is a composition of these independently
executable stages. Actual component-run receipts, rather than the existence of
this wrapper, establish which routes have been executed.

If the independently verified fresh32 application run already exists:

```sh
python3 Solutions/RHOcticPush.v1/finite-pv/grammar/reproduce.py \
  --foundation /absolute/accepted/application32 --out /absolute/fresh/grammar5
python3 Solutions/RHOcticPush.v1/finite-pv/grammar/reproduce.py \
  --verify /absolute/fresh/grammar5
python3 Solutions/RHOcticPush.v1/finite-pv/grammar/controls.py \
  --run /absolute/fresh/grammar5 --out /absolute/fresh/grammar-controls
```

The append independently verifies all foundation source/object/C-resource hashes,
then uses only those exact application objects and pinned generic libraries. It
freshly compiles all four new scientific sources and its auditor. Direct
application import objects must appear in every actual compiler dependency
probe. The separate resource admission requires a 512 GiB host reserve plus a
64 GiB address-space allowance for one compiler, and independently checks disk.
The allowance is not a reservation or a claim of actual peak consumption.

No random seed is used. Exact source hashes, parameters, commands, receipts,
resource measurements, and proof inventories are recorded. Adversarial checks
cover malformed AST components, extra source text, drifted source/object data,
rehash-adjusted omitted or foreign application dependencies, native axiom
injection, missing proof-value endpoints, duplicate JSON, and float/bool metadata.
Only experiment-owned, reproducibly copied mutant directories are removed.
Original source, accepted proof artifacts, and concise verification evidence are
retained. Large prime lists or certificates are neither generated nor required
by this grammar experiment.

## Recorded verification

The accepted fresh append is `counter-grammar-fresh5-v1`: four scientific
modules and its auditor, above the independently source-fresh32 application.
All 186 compiler theorem declarations (42 written plus 144 generated) have only
standard Lean axioms. Nineteen actual proof-value edges connect the inhabited
canonical source-run theorem to all eleven required source/grammar/model
endpoints. The append took 298.735 seconds, with 7,293,536 KiB maximum child
RSS, 7,493,664,768 bytes sampled aggregate RSS, 2,655,245 bytes sampled owned
storage, and zero observed owned-process OOM events. Measurements and their
sampling limitations are in `FRESH_REPLAY_RECEIPT.json` and its actual result.

All 36 actual acceptance CLI controls passed across normal, `-O`, and `-OO`.
Only the verified-regenerable mutant copies were deleted. The original sources,
accepted proof artifacts, source captures, and concise receipts are retained.
`evidence/fresh5-v1` and `evidence/controls-v1` preserve the checked reports;
`SOURCE_FREEZE.json` and `VERIFICATION_SOURCE_FREEZE.json` remain the immutable
scientific and pre-execution verification freezes.
