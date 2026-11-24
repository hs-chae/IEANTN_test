# Complete ordinary-prime bound by prime-square feedback

The four additive Lean files preserve the complete old `L>=35` Box prime-counting
bound, improve its whole function, and prove the clean same-onset `21/50`
subtractive corollary for every real `x>=exp100`. The full lower-scale
`Jupper(L/2)` function is retained, rather than replaced only by a rounded number.
See [the offline rendered derivation](DERIVATION.html).

The exact assumptions are RH, the general integrated Perron explicit formula,
the Nicolas inverse-square spectral bound, and the BPT off-ordinate zero-count
bound. These independently audited published predicates remain visible B-tier
inputs. There is no GM, Buthe, additional numerical premise, or RH-only claim.
This is ordinary kernel mathematics, **not source-first PV**.

## Scientific scope

- `FeedbackPiUpper`: derive `pi(exp s)<=Jupper(s)` for all `s>=35`, then prove
  `Jupper(s)<1.1 exp(s)/s` for all `s>=50`. The upper bound discards positive prime
  powers, so it does not depend on a new ordinary-pi error theorem.
- `FeedbackPrimePowers`: apply that result to the exact square term of the actual
  J-minus-pi identity. Keep the original finite floor-height higher-power tail.
  Above `L=70`, use the full `Jupper(L/2)` in `Qraw`; take `min(oldQ,Qraw)`.
  Below `70`, keep `oldQ`. This retains the entire original `L>=35` domain.
- `FeedbackPi`: connect this correction to actual ordinary prime counting and
  both-endpoint interval differences. The complete new function never exceeds
  the old one and decreases it by more than `1.67 exp(L/2)/L` for all `L>=100`.
- `FeedbackCorollary`: derive the clean `log(x)/(8pi)-21/50` conclusion, with the
  same four canonical source inputs and unchanged `exp100` onset. Its right
  side improves the preceding clean `2/5` bound by exactly `sqrt(x)/50`.
  The full new function is stronger than this convenient clean corollary.

All 39 written theorem/lemma identities are enumerated by `(file,line,name)` in
`SOURCE_FREEZE.json`; all 39 printed transitive axiom closures contain only
`propext`, `Classical.choice`, and `Quot.sound`. The final developer builds passed
in 28.560 seconds total. Developer banks are evidence of proof development,
not the source-fresh acceptance gate. The source-fresh four-file append has now passed over the recursively validated
714-source foundation (718 total scoped sources): 27.432 seconds for actual
compilers and dependency probes, peak child 7,584,180 KiB, 3,298,996 owned bytes
before the result receipt, and zero observed owned OOM events. Recursive
foundation admission/readback time is outside that compiler/probe duration.
`FRESH_REPLAY_RECEIPT.json` records exact result and source hashes. Independent
parent mathematical readback and the 36 actual CLI controls remain separate
gates; no pending control is counted as accepted.

No optimality, global novelty, best-known bound, or measured-prime-error claim
is made. No frozen baseline source, original result, C code, formal AST,
execution model, mathematical assumption or original experiment is changed.

## Reproduction

Use the repository's pinned Lean `v4.34.0-rc2` and pinned dependencies. The exact
compiler, generic library identities, original source plans, source hashes and
all prior proof commands are bound recursively by the existing source-fresh
foundation. Do not substitute a developer `.lake` object bank.

The inherited accepted 714-source foundation consists of the existing 712-source
spectral closure plus the two frozen `spectral-076/corollary` files. Its clean
reproduction commands are documented by that directory and the referenced
`integration/spectral_final` and earlier reproduction scripts. After regenerating
and validating that foundation, execute:

```sh
python3 Solutions/RHOcticPush.v1/spectral-076/feedback/reproduce.py \
  --foundation /path/to/accepted-corollary-fresh2 \
  --out /path/to/new-owned-feedback-fresh4
python3 Solutions/RHOcticPush.v1/spectral-076/feedback/reproduce.py \
  --verify /path/to/new-owned-feedback-fresh4
python3 Solutions/RHOcticPush.v1/spectral-076/feedback/test_reproduce.py \
  --run /path/to/new-owned-feedback-fresh4 \
  --out /path/to/new-owned-feedback-controls
python3 Solutions/RHOcticPush.v1/spectral-076/feedback/build_report.py
```

The fresh compiler sees only copied new source, newly built application objects,
objects from the recursively validated 714-source foundation, and exact pinned
generic libraries. The four new files are compiled sequentially with two Lean
threads and a 64 GiB address-space limit each, preserving a 512 GiB host reserve.
Disk admission is checked independently. Actual compiler dependency probes must
include every declared direct application import and reject foreign application
objects or application objects masquerading as generic libraries. This yields
an exact 718-source scoped closure, independent of the separate Ram606 graph
append.

The validator uses explicit errors, strict integer/resource counters, strict
JSON parsing and finite durations; it does not rely on Python assertions. The
test script executes 36 actual normal, `-O`, and `-OO` CLIs, checks their expected
rejection messages, and retains all decisions and hashes. Relocated positives
are byte-identical artifact readbacks, not new mathematical compilations.

## Evidence and storage

Keep `SOURCE_FREEZE.json`, the four exact Lean sources, reproduction scripts,
source/receipt hashes, concise results, dependency evidence and accepted objects.
The numerical constants are proved in Lean; there are no generated prime lists,
large numerical data files, random seeds or external numerical certificates in
this extension. Control fixtures are deterministic copied artifacts and are
removed only from the test's checked experiment-owned temporary directory after
each actual CLI result is recorded. Original accepted sources, objects and
receipts are never deleted by that cleanup.

Remaining trust is ordinary Lean kernel mathematics with standard axioms,
pinned generic Lean/compiler/runtime/OS/hardware infrastructure, and the explicit
published analytic source predicates above. No executable C/C++/CUDA output or
source-model correctness is claimed by these files.

Usage-guard stop: the new control study is incomplete (11 of36 recorded log
pairs), preserved without PASS. The current invocation drained naturally and
the driver stopped before any new case. Accepted source-fresh718 mathematics
remains unchanged. See `HANDOFF.md` and `evidence/controls36-partial-stop/`.
