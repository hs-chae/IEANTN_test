# Ramanujan continuation: actual li and a stronger source-linked margin

This is a separate post-lock continuation. Original source, outcomes, integer onset and finer root evidence are unchanged. The selected final consumer is `ActualFinalProfile.final_gap_profile` in namespace `RHContinuation.Ramanujan`.

## Completed mathematics

* Proved the actual symmetric principal-value `IEANTN.li` regularization, derivative and offset to `IEANTN.Li` on x>1. No li series/derivative predicate remains in any selected final theorem.
* Derived an actual relative Ei series with its exact additive constant κ, and proved −1/6≤κ≤6/5. The unused equality κ=EulerGamma is not asserted as proved.
* Reproved factorial barriers and global w≤8/5, all eight original finite analytic slabs, and the continuous RH tail. This first gives actual RG≥1/20 on x≥640000000000 and RG≥4/5 on x≥exp42.
* Retained all degree20 positive coefficients, instead of discarding j8..20. The unchanged actual `rh_coeff.c` computes all21 coefficients. Its actual source/AST binding, typed uint64 arithmetic, terminating execution for j0..20 and output correctness are kernel-proved in the reused eight-module component.
* Connected those source-model outputs to the actual li mainterm, discharged the historical `htrunc` gap, and obtained actual RG≥1/12 for EVERY REAL x≥640000000000 (old RG≥.04; improvement factor25/12). All eight stronger margins are kernel interval proofs. Their smallest numerical value is about.087996, with theorem floor1/12.
* Proved a variable analytic remainder, the complete source-polynomial tail envelope and RG≥1+14/L+144/L² for EVERY L≥70. `finalMargin` combines the exact full profile with the stronger convenient floors. `final_gap_profile` consumes it in the actual shifted/squared prime-counting inequality.

All selected proofs depend only on `propext`, `Classical.choice`, `Quot.sound`. They have six explicit mathematical inputs: RH; Büthe2015 Table2, Eq1.8, Eq1.9 and Eq1.10; Büthe2016 Eq7.2. These are the original literature/RH assumptions. No new numerical/analytic success premise, axiom, sorry, native execution axiom or assumed li identity was introduced.

## Exact verification tiers

The degree20 coefficient component is source-first PV:

`rh_coeff.c` → structured AST `CoefficientPV.fn` + checked token/render correspondence → typed64bit arithmetic and loop Run → all21 mathematical coefficients → `ActualSourcePolynomial.actual_source_base` → `ActualSourceFinite.source_finite_log_ray` → actual `final_gap_profile`.

The final source polynomial is defined using actual formal interpreter returned values, not a hardcoded coefficient table. The mathematical polynomial is proved equal to those outputs. Constants in `fullBase_explicit` are later derived by kernel arithmetic, not assumed.

The ENTIRE consumer is a mixed chain: source-first PV for this C coefficient application component, kernel interval proofs for the other finite numerical leaves, and explicit original RH/literature assumptions. It is NOT full source-first PV of prime-count production or of all numerical programs. Exact token/render correspondence is a restricted C frontend, not a proof of a general C parser or compiler. Native C execution additionally trusts the ordinary pinned compiler/runtime/OS/hardware contracts; it is reproduced and hash-bound, with actual outputs checked against the proved application model. Kernel acceptance of the mathematical claims does not trust that native run.

## Reproduce from a clean environment

Use the full published IEANTN checkout containing this directory and `Solutions/RHExposureStudy.v1/Ramanujan640`. Install Python3.11+, a C compiler, pinned Lean4.34.0-rc2, and build generic Mathlib/dependencies at the exact commits in `../scripts/GENERIC_CONTEXT.json`. No original application or LeanCert objects are used; the historical146-module application/checker closure is rebuilt from source.

If generic libraries live elsewhere, make a fresh pinned context:

```
python3 configure_context.py --packages /path/to/.lake/packages \
  --compiler /path/to/lean --out /scratch/generic.json
export IEANTN_GENERIC_CONTEXT=/scratch/generic.json
```

The compiler SHA256 and every dependency commit are checked. `--packages` contains the named Mathlib/batteries/Qq/etc directories from the pinned context. `Cli` executable cache is optional because no selected import uses it. Use fresh experiment-owned scratch outputs:

```
python3 reproduce.py --out /scratch/ram-foundation
python3 control_replay.py --run-dir /scratch/ram-foundation --out /scratch/ram-controls
python3 source_component/reproduce.py --out /scratch/ram-component
python3 reproduce_strong.py --base-run /scratch/ram-foundation \
  --component-run /scratch/ram-component --out /scratch/ram-strong
```

Or `python3 reproduce_strong.py --out /scratch/ram-complete` rebuilds146+10+8+7 sources in one command. Its seven final modules include the dynamic remainder and full profile. Default context is the pinned host path map; the environment override is for a clean relocated build. Source hashes, object hashes, exact commands, dependency-path probes, stdout/stderr, compiler worker RSS and elapsed time are saved in each run. No randomness is used. The source renderer checks the actual C bytes from `include_str`; the C driver executes all21 inputs. `verify.py` uses strict duplicate-free JSON and explicit checks effective under normal, -O and -OO Python. Controls exercise actual CLIs with positive inputs and nine invalid proof/artifact cases plus two invalid invocations in each mode.

Accepted fresh receipts for this session are in `/data/ivy-rh-continuation-20261122/ramanujan/`: `fresh-base-v1`, `final-source-v1`, `source-component-v1`, `strong-source-v2`. `acceptance-controls-v1` predates portability-only script edits; run the current controls for current validator identity. Scripts from earlier accepted runs are preserved in `reproduction_history/` as exact provenance bytes; use current root scripts for clean reproduction, since their relative paths assume this directory.

## Still incomplete

* The original610b/.001 Table1+GM route is written/exact-rational only. Its stronger .076 weighted-J spectral bridge, stronger low factorial barriers and eleven complete slab transports are not all formalized. The actual prime-power rearrangement to `riemannPrimeCounting` is completed separately; it does not discharge those other obligations. The new640b theorem does not complete that earlier-onset branch.
* Full finite source-first PV on [38359837684,640000000000) is open. The historical million interval is disjoint from that missing interval; generic source scalar/checker proofs do not supply the missing actual prime counts.
* `finite_scout/` computes the FULL missing interval with actual native primecount/primesieve, checks row adjacency/strict integer predicates, censuses endpoint-query reuse and can verify deterministic regeneration twice. It is explicitly UNVERIFIED exploration. These outputs never enter the verified network. The saved source and pinned dependencies regenerate large temporary files; only experiment-owned regenerable outputs are removed after the two-run hash and streaming checks.
* The actual finite Mangoldt/log sum is now proved equal to actual `riemannPrimeCounting` for EVERY positive real x. Its exact compensated Abel identity is completed with no analytic identity premise. `ActualGMPrimitive` proves the literal finite primitive equals the actual integral and handles right derivatives at prime-power jumps. `ActualGMTransfer` and `ActualGMClosed` derive the robust actual-J correction14+.2772√x/log²x from the literal FOUR-term published GM bound plus original Büthe anchors. The new `RHPrimeCounting.v1` node provides the actual generic/boxed/B5 signed and absolute-Li consumers with the actual Q correction retained. The stronger.076 spectral transfer remains open.
* A separate old high-count campaign was observed active, but it concerns only one endpoint π(1.49T), not the missing full prefix. It has not been adopted as proof evidence here.
* The signed GM zero-sum/spectral improvement to.076 remains open. It is distinct from the completed robust.2772 primitive transfer and actual-J identification; the new transfer does not complete the610b branch.

No best-known, optimality or full finite source-first-PV claim is made. The onset640b is retained; the mathematically stronger result here is a quantitative all-real margin and a completed li-definition/source-coefficient connection.

For the additional actual-J/GM/canonical nodes, run:

```
python3 node_publication/reproduce.py --strong-run /scratch/ram-strong --out /scratch/ram-nodes
```

This freshly compiles14 selected appended sources and all four RamanujanGap.v3 plus seven derived RHPrimeCounting.v1 typed consumers; the GM source conclusion itself is literature-backed, not claimed proved by the solution. Read `GM_TRANSFER_PROOF.md` for the exact source formula and every endpoint/domain/rounding allowance.


Before running a long replay in a relocated environment, check the source layout, compiler pin and full pinned generic object inventory:

```
python3 reproduce.py --check --check-generic
```

This check passed in the present continuation with a newly generated relocated context. It checks generic dependencies only; it does not substitute for the fresh application/checker replay. The selected final source replay is `node-publication-v9`, after the unconditional lower-height prime-power series and nonnegativity exports were added. Earlier append receipts remain historical evidence.

`evidence/README.md` describes the compact preserved scientific evidence and its exact hash inventory. No compiled application object bank is necessary in the downloadable evidence: all such objects are deterministically rebuilt by the reproduction scripts. Accepted server-side proof artifacts are retained. The complete native finite scout has independent clean bootstrap instructions in `finite_scout/README.md`; it remains unverified numerical exploration.
