# Local `native-assisted` gate (non-official)

This checks named program-verification endpoints and writes **local research attestations** to
`pv-evidence/`. It is not Comparator. It never writes to `receipts/`, never sets
`lean-comparator`, and is not wired into `scripts/verify-comparator.sh`. The design is in
[docs/program-verification/NATIVE_ASSISTED_DESIGN.md](../../docs/program-verification/NATIVE_ASSISTED_DESIGN.md).

| File | Role |
|---|---|
| `Extract.lean` | Run with `lake env lean --run` inside a solution project. Writes facts about one endpoint: its type (`pp.all` and a binder-erased canonical form), its hypotheses, its transitive closure, every axiom with type and source range, native-fact data, embedded `String` literals, and the `.olean` each project module was loaded from. Makes no judgement. |
| `native_assisted_check.py` | Builds the project, runs the extractor on the solution and on the generated challenge, applies the policy, and writes `pv-evidence/<key>.native-assisted.local.json`. |
| `semantics.json` | The **reviewed** registry: allowed native tactics, the source-association, execution and correctness constants that count for `lean-verified-program`, library roots, the trust boundary and the promotion rule. |
| `endpoints.json` | The audited endpoints. Each has a Lake project, a root module, the endpoint theorem, the challenge module and the executed C files. |
| `controls.py` | Lean-level controls. It copies the pilot to a scratch directory, adds fixture theorems and mutates sources, then checks that the gate gives the expected verdicts. The repository is hashed before and after. |

## Commands

```bash
python -m venv ../tools && ../tools/bin/pip install -r requirements-dev.txt   # pyyaml
lake exe cache get && lake build                                             # core, pinned toolchain
# each solution project: link the shared packages or run `lake update`, then build
python scripts/native_assisted/native_assisted_check.py check RamanujanNumerics.v2.epsilon_budget
python scripts/native_assisted/native_assisted_check.py check-all
python scripts/native_assisted/controls.py
python -m unittest tests.test_native_assisted tests.test_pv_metadata
python scripts/ieantn.py check            # now also validates pv-evidence/ (fail-closed)
```

`check` exits 0 for passed, 1 for failed and 2 for blocked. An attestation records the endpoint,
statement hashes, the challenge match, every native fact (owning theorem, module, source file and
SHA256, range, token, decided proposition, count of trusted library implementations), the method
checks S/A/E/C/M, a proof-closure fingerprint (statement + SHA256 of every project module in the
closure), pins, commands, timings and the official status. The official status is read from
`formalization.yaml` and `receipts/`.

## What `passed` does and does not mean

**It means.** The pinned build succeeded. The solution theorem states the challenge, up to binder
names. Every axiom in the proof is one of the three standard axioms or an audited `native_decide`
fact.

**It does not mean.**
- It is not official IEANTN verification and not a Comparator receipt.
- It is not compiler, runtime or hardware correctness.
- It is not a proof that a compiled C binary matches the restricted C model.
- It does not prove the endpoint's listed mathematical hypotheses.
