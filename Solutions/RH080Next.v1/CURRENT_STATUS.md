# Current proof and numerical status

Branch: `hs-chae/IEANTN_test`,
`research/rh080-primal-dual-explicit-pv-20261125`.
Frozen predecessor: `1c668b75`. Its original 20 primary trials and eight
follow-up outcomes remain unchanged. This is additional, posthoc research.

## Completed scopes

| Result | Exact statement or boundary | Verification |
|---|---|---|
| Full CMS obstruction | Functional quotient at least `100/123`, strictly above `4/5`, for the full real-even CMS class | 49-source cold build; original actual C, independent syntax, execution, numerical enclosure and full-class consumer |
| Better Gaussian | Limsup normalized gap at most `20582561296/24680948495`; strict eventual bound `< 0.833945313`, below v3 | 92-source cold build; 1,124 cells, actual Fourier transform, infinite tails and full CMS consumers; RH plus the named CMS reduction; **kernel-only, not PV** |
| Two population curves | For every nonnegative parameter, eventual width `min(0.944247 + 1.163388 α, 9/8 + (16/15) α)`; `2.108` at α=1, `283/24` at α=10 | 91-source cold build; actual C programs, independent syntax/execution/numerical proofs, full Fourier/prime-count consumers; RH plus two named BR source propositions |
| Small-x bridge | Open intervals at coefficient `0.777` on `[4,11)`, `0.74` on `[11,4·10^18]`; coefficient `0.8` through `exp(42)` | Kernel proofs conditional on historical consecutive-prime input CMS(1.15); no newly verified historical prime search |
| Original-window scalars | Actual w4 and Fap mass, moments, variations and height computations | Combined fresh 58-source scalar build; corrected-header J adapters and maxima compile; all original final transfer consumers consume these outputs |
| FFT mathematics | Exact transform/cosine identity, root errors, long twiddle recurrences and rounded-error budgets at 2^17 and 2^24 points | Twelve-source cold builds in Python normal, `-O` and `-OO`, 51 audited roots; exact signed multiplication/addition/division/increment arithmetic; **not complete C FFT execution proofs** |

Accepted proof closures use only `propext`, `Classical.choice` and
`Quot.sound`. Literature propositions remain explicit hypotheses.
No official Comparator acceptance receipt is authored here.

Both population curves are **eventual**, with no explicit onset. They do
not inherit the previous octic theorem's `exp(24)` threshold. Their leading
coefficients improve that old leading frontier in its overlapping coefficient
range; no best-known claim is made for all population parameters. Matched
kernel-only controls prove the **same** curves: PV adds a verified source
connection, not an established causal gain in mathematical strength.

## Stronger independently checked frontier

Exact new step witnesses give functional lower bounds `2000/2399` for
penalty 36/11 and `5000/5877` for penalty 4. Each has both a directed-Arb
DFT enclosure and an independent non-FFT complex-Horner enclosure. Exact
executed inputs, receipts and compressed interval certificates are under
`dual/inputs` and `dual/evidence`.

These stronger bounds are **native-assisted interval calculations, not Lean
or source-first PV**, and are not promoted to verified nodes. The published
bound is `50000/60393`; the source-first kernel bound remains `100/123`.
No optimality is asserted. The kernel obstruction already excludes 0.8
within this CMS budget; it does not exclude every different RH argument.

## Principal remaining obligations

The entire analytic transfer is proved: Fourier/support-seven estimates,
signed logarithmic moment, Mellin/zero/pole/trivial-zero terms, actual prime
powers and Montgomery–Vaughan wings, continuous ranges, and strict prime
endpoints. All six original consumer/audit modules compile from the two
original norm bounds. The original weighted curve also has a genuine strict
coefficient-infimum corollary for every nonnegative population parameter.
These norm arguments remain explicit in this checkpoint's published original
consumers; see `explicit/REMAINING_B.md`.

The separate full 131,072-point integer FFT trace has now passed a fresh
kernel replay, and finite-interval norm/consumer integration is being checked
for the next publication checkpoint. That work is **kernel-only** until the
actual C execution refiner consumes the same trace.

The source-first C migration remains incomplete. Full copy and typed-zero
helpers passed a fresh 50-source replay, magnitude comparison passed fresh
49-source replays, and the generic argument-order theorem passed seven fresh
sources. The C scalar providers already have complete consumers. The
original FFT programs still need their remaining arithmetic/full-call,
recursion, actual caller initialization and source-linked output proofs.
Canonical root-initializer executions do not establish their applicability
to the main function's same-allocation work/root slices. No full FFT PV claim
is made. Consult `pv/README.md` and its exact publication manifest.

The finite claims use **Fap**, mesh 80/support 5; the global ray uses the
different mesh-360/support-7 **w4** input. Exact original algorithms,
independent grid sizes, parameters and hashes are recorded in
`explicit/LOCKED_PROFILE_PROVENANCE.json`. No new prospective four-arm
discovery experiment is complete; the original locks remain unchanged.

## Reproduction and trust

Use the compiler and eight generic package commits pinned in
`../RH080Study.v1/estimates/DEPENDENCY_PINS.json`. A context JSON identifies
the compiler and generic library directories. Scripts check identities and
rebuild every application source without historical application objects.
From the repository root:

```sh
python3 Solutions/RH080Next.v1/dual/reproduce_dual.py --repository "$PWD" --context /path/to/context.json --run /fresh/dual --workers 4
python3 Solutions/RH080Next.v1/dual/reproduce_fft_math.py --repository "$PWD" --context /path/to/context.json --run /fresh/fft-math
python3 Solutions/RH080Next.v1/primal/population/reproduce.py --context /path/to/context.json --out /fresh/population --workers 2 --worker-memory-gib 64
```

The scoped directories include further source regenerators, full
reproducers, exact hashes, receipts and resource records. Physical compiled
observations retain explicit compiler, ABI, runtime/API, OS and hardware
contracts. Restricted C semantics do not prove ISO C adequacy, compiler
correctness or a physical hardware trace. A helper execution does not
certify its entire caller. Large scalar proofs need tens of GiB; use actual,
separately measured RAM/disk capacities. Clean only checked-regenerable,
experiment-owned scratch; preserve source and essential evidence.
