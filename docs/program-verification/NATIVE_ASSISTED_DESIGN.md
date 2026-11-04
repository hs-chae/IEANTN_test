# `native-assisted` and `lean-verified-program`: design

Status: local research infrastructure on branch `agentB/native-assisted` of `hs-chae/IEANTN_test`.
It changes neither official IEANTN trust semantics nor any receipt.

## 1. Three questions, kept on three separate axes

| Axis | Question | Values | Where it is stored |
|---|---|---|---|
| **Official justification kind** (unchanged) | What does the official IEANTN trust graph rely on? | `lean-comparator`, `lean-noncompliant`, `numerical`, `literature`, `asserted`, `bridged`, `none-yet` | `formalization.yaml`, `justifications[].kind` + `designated` |
| **Evidence method** | *What* did the proof verify? | `lean-verified-program`; anything else is reported as `not-program-verified` | the local attestation, and optionally `justifications[].verification_method` (validated, see §4) |
| **Local gate** | *How far* has the proof been admitted? | `native-assisted: passed / failed / blocked / not-run` | `pv-evidence/<Node>.<conclusion>.native-assisted.local.json` |

- **No kind is added or changed.** In particular there is no `lean-verified-numerical` kind. A pure
  Lean proof of a numerical inequality is an ordinary Lean proof.
- **`lean-verified-program` is a method, not a trust tier.** It records that a real source program
  was associated with a formal program, that its modelled execution was linked to an output, and
  that a Lean correctness theorem takes that output to the mathematical statement.
- **`native-assisted` is a local admission tier.** It is weaker than official `lean-comparator` and
  never substitutes for it.

## 2. Definitions

**`lean-verified-program`.** It is recorded for an endpoint theorem `T` only if `T`'s transitive
proof closure contains all five of:

- **(S) source identity**: a `String` literal (from `include_str`) whose bytes equal the configured
  C source file on disk;
- **(A) source association**: a proved fact whose statement reaches that literal and a reviewed
  association function (token matching), following definitions;
- **(E) execution witness**: a proved fact whose statement reaches the same literal and a reviewed
  execution relation or evaluator;
- **(C) correctness**: a reviewed generic correctness theorem, for example
  `SumStability.c_sum_forward_error_real` or `ForwardRamanujan.source_linked_upper`;
- **(M) a mathematical endpoint**: `T`'s statement mentions no program-level constant.

The reviewed names are listed in `scripts/native_assisted/semantics.json`, and adding one is a
review decision. The test is about *this proof*: a numerical certificate that never uses the
program does not qualify, even when a program exists nearby.

**`native-assisted: passed`.** All of the following hold for the named endpoint, freshly rerun:

1. `lake build <root>` succeeds at the pinned toolchain.
2. The solution theorem has the same statement as the generated challenge, up to binder names
   (α-equivalence).
3. The transitive axiom closure contains only:
   - `propext`, `Classical.choice`, `Quot.sound`; and
   - finite native-evaluation facts whose provenance is audited (§3).
4. There is no `sorryAx`, no other axiom, no `unsafe` declaration, no other native mechanism, and no
   project `implemented_by`/`extern` reachable from the closure or from a native fact's evaluated
   expression.

`failed` means a check found a violation. `blocked` means the check could not run or provenance
could not be decided; either way, never a pass. `not-run` means nobody has run it.

## 3. What counts as an audited native fact (this toolchain)

Lean `4.34.0-rc2`, in `Lean/Meta/Native.lean` (`nativeEqTrue`), handles every `native_decide` call
the same way:

1. it compiles and evaluates a closed `Bool` expression `e`;
2. it then adds an **axiom** `<D>._native.native_decide.ax_<i>_<j> : @Eq Bool e true`;
3. it records the axiom's declaration range as the tactic syntax.

The gate accepts such an axiom only when all of these hold:

- the name has that form and the tactic is `native_decide` (allow-list);
- `D` exists, is a theorem, and is declared in the same project module as the axiom;
- the type is exactly the closed `@Eq Bool e true` shape;
- the declaration range resolves to exactly one source file and the text there is the token
  `native_decide`. An `axiom` command given a native-looking name fails here, and a control shows it
  (`FakeNative`);
- `e` reaches no `implemented_by`/`extern` declared in a project module. Library implementations
  (Lean core, Std, Batteries, Mathlib) are counted and listed per fact as trusted runtime.

The mechanism is toolchain-specific. The checker classifies axioms by inspecting the actual
declarations; it does not match a spelling. A different mechanism (`Lean.ofReduceBool`,
`Lean.trustCompiler`) is reported as `blocked` until it is reviewed.

## 4. Metadata: the smallest backward-compatible extension

- **Sidecar attestations.** These are machine-readable files in `pv-evidence/`. They are never
  placed in `receipts/`, and each carries the notice *"Not an IEANTN verification receipt"*.
  `ieantn.py check` validates them fail-closed (`check_pv_evidence`):
  - the notice must be present;
  - the status and method must be known values;
  - the recorded designated kind must equal the yaml;
  - the receipt status must agree with `receipts/`;
  - `passed` must have no rejected axiom.
- **Optional `verification_method` on a justification.** Today the parser silently ignores unknown
  justification keys, so this field is now validated explicitly:
  - the value must be `lean-verified-program`;
  - the kind must be `lean-comparator` or `lean-noncompliant`;
  - a sidecar must exist that records the same method.
  The field changes no trust computation. It is used only on non-frozen nodes, because frozen
  metadata is byte-identical by policy.
- **Node pages, opt-in.** Rows are added only when a sidecar exists: `Evidence method`,
  `Local gate`, `Official IEANTN classification`, `Official Comparator receipt`, and a link to the
  attestation. Every other page renders byte-identically (checked over the whole network).
- **Untouched.** `status`, `graph`, `check-graph`, `check-closure`, `gen-challenges` and
  `fingerprint` compute exactly what they did before. There is no parallel trust graph.

## 5. Promotion rule (policy, not automation)

- **No automatic promotion.** No local attestation promotes anything.
- **Route to `lean-comparator`.** A conclusion's official kind may become `lean-comparator` only
  when the verification workflow records an authentic Comparator receipt for the same conclusion.
  That requires a proof whose closure is exactly the three standard axioms, so the native facts
  must first be replaced by kernel-checked evidence.
- **The method label survives promotion.** `verification_method: lean-verified-program` may be
  kept as a description.
- **Not implemented.** A receipt-backed *official* subtype `lean-verified-program` would need an
  upstream schema and Comparator policy change.
- **No replacement of stronger justifications.** Where a conclusion already designates
  `lean-comparator` (for example `DudekPlattNumerics.v4.pi_two_sided_footnote`), a program-verified
  route may only be added as an extra, non-designated record.

## 6. What `native-assisted` admits that Comparator does not

- the correctness of the Lean compiler and runtime on each listed finite evaluation (and of the
  listed library `implemented_by`/`extern` implementations);
- that is all. Each fact is still a closed, finite, decidable proposition, evaluated during the
  build of a hashed source module.

The following remain trusted under both tiers: the restricted C / IEEE binary64 round-to-nearest
model, as a description of what a real C compiler does; the compiler; the host runtime; the
hardware; and the explicit mathematical hypotheses of each endpoint.

## 7. Incompatibilities and limits found

1. **Lake does not trace `include_str` inputs.** After the C file changes, `lake build` replays
   the old object with the old embedded source and still exits 0. A green build therefore does not
   prove that the proof refers to the current C file. The gate's (S) check compares the embedded
   literal with the file on disk and catches this; see the `ChangedInputLiteral` control.
2. **Module-name ambiguity.** Many solution packages define a module called `Solution`. The
   extractor puts the target package's build directory first in the search path and records which
   `.olean` it loaded.
3. **Generated pages link solutions at `teorth/IEANTN`.** On this fork those links return 404.
   This is inherited and not changed here.
4. **No official subtype.** `verification_method` is IEANTN-local. Palomar strips `conclusions`
   before validating, so the field does not affect Palomar.
