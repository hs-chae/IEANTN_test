# IEANTN

The **Integrated Explicit Analytic Number Theory Network**: a graph of claims about explicit
analytic number theory, together with a record of how well each one is justified.

Explicit analytic number theory is a field of long dependency chains. A bound on `π(x)` rests on a
bound on `ψ(x)`, which rests on a zero-free region, which rests on a numerical verification of the
Riemann hypothesis to some height — and in the published literature those dependencies are recorded
only in prose, if at all. Some links are fully rigorous, some rest on very large computations, and
some rest on claims a paper states without proof.

This repository records that structure explicitly. Each **node** makes a mathematical claim,
declares what it assumes, and carries evidence for the step from its assumptions to its claim. The
evidence may be a Lean proof checked by [Comparator](https://github.com/leanprover/comparator), a
numerical computation, or a citation. The goal is not that everything is certain — it is that **for
any result you can read off exactly what it rests on and how good that evidence is.**

## Local maximal PV evolution experiment

The new isolated Agent A work is described in [the provider handoff](docs/qrh/PV_EVOLUTION_AGENT_A.md). It preserves the frozen Scoped inputs and comparisons, distinguishes numerical execution from analytic gains, and identifies the subsequent Agent B vocabulary/node integration. See the accompanying reviewed source/evidence bundle for actual acceptance; no official status or publication is implied.

## QRH experiment branch: start here

This `qrh-2pv` branch contains the QRH/CH2 propagation experiments, the paired
Table 4 program verification, and a completed controlled forward Ramanujan pilot.
**New agents should read [the branch handoff](docs/qrh/README.md) first**, then the
repository guidance below. It distinguishes checked proofs, explicit assumptions,
finite native facts, external replay artifacts and the next implementation task.
[Reproduction](docs/qrh/REPRODUCING.md) and [offline rendered results](docs/qrh/RESULTS.html)
are included. Core builds do not check the separate solution projects.

## The central idea

Every node's challenge is a **conditional theorem**: *if* the results it imports hold, *then* its
own conclusions hold. Whether the node itself is justified is **metadata, not Lean**.

So a node backed by a one-line citation and a node backed by a 200,000-line machine-generated proof
have the same shape, and nodes import each other's *statements*, never each other's *proofs*. The
Lean layer certifies only the **edges** of the graph; the standing of the graph as a whole is a
separate, auditable question.

## Layout

```
IEANTN/Vocabulary/               the shared language — definitions only, Mathlib-only
IEANTN/Nodes/<Family>/<version>/ Conclusions.lean, Challenge.lean, formalization.yaml,
                                 and optionally Tables.lean for a paper's bulk data
IEANTN/Bridges/<Family>/         proofs that one version's conclusions imply another's
Solutions/<Family>.<version>/    proofs — separate Lake projects, not in the core build
receipts/                        one JSON file per Lean-verified conclusion
build-records/                   one JSON file per locally compiled solution conclusion; not
                                 receipts (see "Structure: computed results")
<node>/fingerprints.json         generated and committed, so a change of meaning is a diff line
STATE.md, GRAPH.md, docs/nodes/  views of the metadata, written by CI on `main` — see
                                 CONTRIBUTING.md; do not commit them from a branch
docs/                            ARCHITECTURE.md, NODES.md, ROADMAP.md, SOURCES.md,
                                 SOLUTIONS.md
```

The core build is Vocabulary and Nodes only, and is deliberately fast. Solution verification is a
separate, dispatchable workflow: running Comparator on every pull request would take hours and
defeat the purpose of the split.

## Structure: computed results

A result that comes from running a program has three parts here, and each is checked separately.

1. **The statement**: `Conclusions.lean` in the node. Consumers import it as a hypothesis, as for
   every other result.
2. **The proof**: a Lean project under `Solutions/<node>/`. For a computed result the proof usually
   contains the program. The C source is embedded with `include_str`, matched to a Lean model of
   the program, and the model's run is evaluated in Lean, by the kernel or by `native_decide`.
3. **The record of the computation**: in `formalization.yaml`, on the justification.

```yaml
- id: source-transport
  kind: lean-noncompliant
  reason: native_decide        # why there is no receipt: native_decide | workflow-cannot-run
  computation:                 # what the number came from; check re-hashes every file named
    files:
      - {path: Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c, role: program, sha256: 0685e913...}
    output: "0x3cc0fd404ee3d945"
  note: ...
```

Each conclusion then has one grade of evidence, which `status` and `report` show:

| Grade | What it means | Written by |
|---|---|---|
| Comparator receipt (`lean-comparator`) | Verified. The verification workflow compiled the proof, matched its statement to the challenge, and found only the three standard axioms. | the verification workflow, in `receipts/` |
| Current build record | The proof compiled here and states its challenge, and every file it was built from is unchanged since. Each `native_decide` step it relies on is listed by name. | `python scripts/ieantn.py build-record <node>`, in `build-records/` |
| Not built | A Lean proof is claimed (`lean-noncompliant`), but nothing here has compiled it. | nobody yet |
| External computation | `numerical`: the computation ran outside Lean. Its `computation` record names the program and its hash, or a URL and any published checksum. | the node's author |

`build-record <node>` compiles a solution as the verification workflow does: the package's default
targets, then the solution module. First it forces every Lean file that embeds a file with
`include_str` to recompile, because Lake does not track those files and would otherwise replay a
build made from an older program. It then checks that the solution theorem states exactly the
generated challenge, lists every axiom the proof uses, and writes
`build-records/<Node>.<conclusion>.json` with the SHA-256 of every Lean module, embedded file and
Lake configuration file the proof was built from.

`check` runs on every pull request, compiles nothing, and re-hashes files:

| Situation | `check` |
|---|---|
| The record passed, the statement matches, and every hashed file is unchanged | ok |
| The record says the build failed, or the statement differs from the challenge | fail |
| A file the record hashed has changed or gone | fail: stale, re-run `build-record` |
| `lean-noncompliant` with no build record | ok, listed as not built |
| `lean-noncompliant` without `reason`, or with any other value | fail |
| `reason` disagrees with the record: `native_decide` steps listed but another reason given, or the reverse | fail |
| A file named in `computation` is missing or its hash changed | fail |
| A build record for a conclusion that does not exist | fail |

A build record is not a receipt; only a Comparator receipt counts as verified. A proof that uses
`native_decide` cannot get a receipt under the current rules, so a current build record is the
strongest evidence it can have, and the steps it lists are trusted, not checked by the kernel. A
`workflow-cannot-run` proof uses standard axioms only and needs a runner that can finish it. In every
case the compiler and operating system stay trusted for any real run of a program, and so do the
programs behind `numerical` results. `python scripts/ieantn.py check` lists the `lean-noncompliant`
conclusions that are not built yet.

## Reading order

0. [GRAPH.md](GRAPH.md) — **the network itself**: what it contains, what each result rests
   on, and what is taken on trust. Generated, and the place to start if you only want to
   see the thing. Each node also has a generated summary page under
   [docs/nodes/](docs/nodes/README.md): what it claims, in Lean and in prose, and everything
   recorded about why it should be believed.
1. [CONTRIBUTING.md](CONTRIBUTING.md) — the ten things people actually do, and how.
2. [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) — the design and why it is what it is.
3. [docs/NODES.md](docs/NODES.md) — node file formats, in detail.
4. [CLAUDE.md](CLAUDE.md) — the short version, for coding agents.
5. [docs/ROADMAP.md](docs/ROADMAP.md) — what is deliberately not built yet, and why.
6. [docs/SOURCES.md](docs/SOURCES.md) — the papers the nodes rest on, held and wanted.
7. [SECURITY.md](SECURITY.md) — the trust model, and what a forged receipt would take.

## Status

Early, but the machinery is in place and exercised. Vocabulary, three proof-of-concept node
versions and the bridge between two of them, challenge generation, statement fingerprints,
verification receipts, the breaking-change detector, the network checks and the housekeeping queue
all exist and run in CI.

**The Comparator path works end to end**: `Lcm.v1` carries a receipt written by the verification
workflow, and `ieantn.py status` grades it against the current environment.

Outstanding: visualisation, the `/verify` comment trigger, and the composing half of the
Palomar spin-off generator. [docs/ROADMAP.md](docs/ROADMAP.md) tracks what is deliberately not built
and why; [SECURITY.md](SECURITY.md) states the trust model.

## Claiming a task

Open work is tracked on the [**IEANTN project board**](https://github.com/users/teorth/projects/3).
Anything marked `Unclaimed` is free to take: comment `claim` on the issue and a bot assigns it to
you and moves the card. `disclaim` releases it again, and `propose PR #123` links your pull request.
Claims do not expire, so please release one you are no longer working on.

This work grows out of the IEANTN subproject of
[PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), whose blueprint-based structure
it is intended to replace; discussion is on the
[`#PrimeNumberTheorem+`](https://leanprover.zulipchat.com/#narrow/channel/423402-PrimeNumberTheorem.2B)
Zulip channel.

## Building

```bash
lake exe cache get
lake build
```

One `declaration uses 'sorry'` warning per node conclusion is expected. A challenge states; it does
not prove.

## Scoped QRH numerical-program demonstration

See [the scoped Winner provider guide](docs/qrh/SCOPED_WINNER_AGENT_A.md) for the conditional prime-error bound with coefficient 0.00947147, frozen 39-identity comparison, source entrypoints and trust/reproduction limits. This is a native-assisted local research provider; no official receipt is implied.
