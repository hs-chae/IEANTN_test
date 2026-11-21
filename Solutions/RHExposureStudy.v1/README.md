# RH propagation: two independent research arms

[Delivery and handoff](DELIVERY_AND_HANDOFF.md) records the exact uploaded files, archive hash and one-command restoration. [ARTIFACTS.json](ARTIFACTS.json) contains the verified attachment identities.

Read `reports/RH_PROPAGATION_REPORT_EN.html` or `reports/RH_PROPAGATION_REPORT_KO.html`. Both are standalone offline documents with static mathematics. They distinguish the original independent submissions, later reviews, and coordinator proof completion. Start with `ledgers/RESULTS.json` for exact statements, domains, assumptions, evidence and remaining obligations.

This is an isolated research solution directory. It does not replace existing IEANTN results or assert that RH has been proved. The actual RH node and logical adapters are in the repository's `IEANTN/Nodes/RH*` and `IEANTN/Bridges/RH` directories.

## Completed mathematics and its boundary

* The actual all-real Ramanujan consumer gives `RG(x) >= 1/25` for `x >= 640000000000`. The exact remaining inputs are RH, Büthe's specified statements and two standard bridges from the actual principal-value `li` definition to its series and derivative. The new finite and infinite-tail obligations are proved. The stronger 610-billion proposal remains separately written, not covered by this proof.
* `MertensPositive.first_mertens_positive_IEANTN` proves `A(x)-log(x)-E > .006/sqrt(x)` on the full closed band `[exp(24),10^19]`, conditional on RH and five exact original-publication predicates. Every new convergence, finite Abel, full-prime correction, integration and scalar step is proved.
* Under RH, the post-lock forward corollary gives more than (1+.04/logu)*sqrtu primes in (u,u+2.43sqrtu logu) for every realu>=exp24. Its exact whole-ray conversion was independently checked. The final NL parabolic PNT and interval results are independently reviewed written mathematical results. They have exact-rational numerical support, not a complete formal analytic source-first proof.
* Existing C source-linked count outputs are genuinely consumed by the new local real-crossing proof. The broad finite C++ count is native evidence. The small new coefficient C function has a source-linked component proof and conditional polynomial consumer; it is not used by the completed 640-billion theorem.

Here **PV means source-first program verification**. Lean arithmetic, `native_decide`, kernel certificate verification and ordinary native computation are not called PV. Standard axioms alone do not discharge theorem parameters. See each printed final theorem type and the trust/gap ledger.

## Directory map

* `locked/NL_RH/` and `locked/IEANTN_RH/`: exact original final submissions and coordinator byte locks. Do not edit these. Corrections and later proofs are separate.
* `protocol/`: pre-registered two-arm protocol, identical mathematical mission, actual packet/runtime/source inventories and neutral literature rules.
* `MertensPositive/`: minimal standalone proof sources, exact retained source formulations, normal/-O/-OO receipts and offline full proof.
* `Ramanujan640/`: completed post-lock proof sources, raw rational leaves, source/rounding transport, exact theorem types, clean replay and acceptance controls. Earlier cached-dependency receipts remain historical and are distinguished from the later source-only replay.
* `review/`: independent final mathematical reviews, source corrections and stronger literature comparisons; none was supplied to discovery workers.
* `ledgers/`: result, reuse, input/source, resource and gap records.
* `evidence/`: preflights, matched timed checkpoints, final locks, original failures, source-service repair and replay receipts.
* `scripts/`: deterministic checking/reproduction and the recorded experiment machinery. Discovery requires model access; proof replay does not.

## Reproduce from a clean environment

Use Linux x86-64, Python 3.10 or newer, Git and elan. The source bootstrap pins Lean `v4.34.0-rc2`, Mathlib `71a80585ee495fc24472fd0eaffc89d94e4fd8d6` and all its recorded dependency commits. Generic Mathlib caches are permitted; old application proof objects are not required for the two completed consumers. Sufficient disk/RAM is needed for Mathlib and proof compilation. There is no four-GiB cap.

From this directory:

```sh
python scripts/bootstrap_generic.py --out /absolute/fresh/generic-setup
python MertensPositive/replay.py --context /absolute/fresh/generic-setup/GENERIC_CONTEXT.json --out /absolute/fresh/mertens-normal --optimize normal
python -O MertensPositive/replay.py --context /absolute/fresh/generic-setup/GENERIC_CONTEXT.json --out /absolute/fresh/mertens-O --optimize O
python -OO MertensPositive/replay.py --context /absolute/fresh/generic-setup/GENERIC_CONTEXT.json --out /absolute/fresh/mertens-OO --optimize OO
```

`Ramanujan640/README.txt` gives the exact source-only V2 command and source selection. It regenerates the original numerical leaf data and rebuilds the accepted application/checker closure using only pinned generic libraries. Read its exact retained `li` and literature hypotheses before interpreting the result. The old V1 rebuild consumed explicit inherited objects and is not mislabeled a source-only replay.

If the pinned generic environment already exists, validate its actual binary and dependency identities without downloading:

```sh
python scripts/bootstrap_generic.py --existing-context MertensPositive/BUILD_CONTEXT.json --out /absolute/fresh/validated-generic
```

Replace the historical host paths in an explicit context file when running on another machine; retain all compiler and commit pins. Local receipts identify which bootstrap route actually ran. The generic download route is provided for clean preparation; it is not a claim that the toolchain or physical hardware was proved from first principles.

## Reproduce the original submissions

The original `verify.sh` (NL) and `reproduce.py` (full) are preserved under each locked portfolio. Their `/task`, `/generic`, `/ieantn` and `/application-cache` paths describe the actual isolated runtime. The recorded namespace spec and `scripts/replay_locked_portfolio.py` reproduce them in that layout. Both final original reproducers were independently rerun offline with fresh new objects. The full original reproducer explicitly uses the pinned inherited application bank; a source-only proof of the new consumers is a separate route.

Several original exploratory numerical scripts use Python `assert`. Their original normal-mode runs had assertions active. Do not run them under optimization and assume the same acceptance gates remain. The independent reviewer and final acceptance scripts instead use explicit checks, and their actual normal/-O/-OO CLI controls are retained. Numerical originals and validator revisions have separate hashes.

The NL C++ workload is regenerated by its original source:

```sh
g++ -std=c++17 -O3 -march=x86-64 -pthread locked/NL_RH/files/finite_ram.cpp -o /absolute/fresh/finite_ram
/absolute/fresh/finite_ram 1630650286564 8
```

This completed native rerun verifies reproducibility of the numerical evidence; it does not prove C++ source/semantics correspondence. No random seed is used by these deterministic numerical algorithms. The research model configuration and nominal paired seed are in the protocol; repeating model discovery need not reproduce its exact output.

## Preserve the comparison

There are exactly two exposure arms. Historical QRH and known RH literature are reference baselines. The coordinator's positive Mertens result, source-only 640-billion proof completion and post-lock CH finite-height comparison are not additional arms or retroactive discoveries. Technical minute snapshots are not atomic final submissions. Scientific checkpoints at 900/1800/3600 seconds were fixed before work; final portfolios took different total elapsed times.

The initial common source-helper schema defect and unequal early failed-request costs are preserved. The corrected broker restored the same intended literature policy for both arms. No general stochastic advantage, optimality, best-known-result or necessity-of-PV claim is established by this single pair.

## Storage and continuation

Large prime lists and search outputs are not needed for the completed analytic consumers. The compact source/certificate data, original outcomes, exact parameters, source locators, receipts and hashes are retained. Only verified experiment-owned regenerable duplicates may be removed; never remove locked inputs, accepted proof sources or unrelated workspaces. `ledgers/CLEANUP.json` records actual cleanup, if any, separately from proposed targets.

The remaining source-first Ramanujan finite prefix, two actual-`li` definition bridges, full analytic formalization of the 610-billion/NL routes, and explicit spectral-input formalizations remain identified tasks. They are not a request to complete every IEANTN placeholder.

## Git source versus companion evidence

Following the repository handoff convention, the branch publishes reviewed source, mathematical statements, reproducibility scripts, compact records and the readable reports. Complete compilation ledgers, raw replay/checkpoint evidence and original run logs remain in the separately delivered evidence bundle. Restore that bundle into a fresh directory to obtain the exact full study tree and all local report links; do not overwrite an existing checkout. The two completed proof consumers can rebuild from the published source and pinned generic inputs. Full exposure repetition additionally needs the retained legacy application bank and authenticated native model runtime, explicitly listed in ledgers/REPRODUCIBILITY_STATUS.json. No official Comparator receipt or verification designation is created here.

Original external papers, page captures and full extracted texts stay in the research source store. The downloadable study provides exact hashes and versioned primary-source references in ledgers/EXTERNAL_SOURCE_DOCUMENTS.json and the source ledgers. Their statements and the new proofs are rendered in the reports; no complete external paper is required by the completed Lean replays.
