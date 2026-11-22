# Compact prime windows, absolute Mellin moments, and source-first C logarithms

This is new post-lock RH continuation research. Historical RH exposure sessions,
controls, results, sources, and their proof status are unchanged. See
[CLAIMS_AND_GAPS.json](CLAIMS_AND_GAPS.json) before using any result.

## Mathematical results and exact boundaries

The strongest direct prime-count construction uses the octic physical kernel
`max(0,1−u⁸)`. For every real u≥e²⁴ its written RH argument gives more than
`(9001/9000+5.8/log u)√u` primes in a forward interval of width
`2.15√u log u`. A full parameter family covers widths C∈[1.03,16] with count
`(8C/9−.911+4.2/log u)√u`. The actual prime-count Lean consumers compile with
only the standard three axioms. Their precise explicit-formula, zero-sum,
prime-power, trivial-term, scalar-geometry and whole-ray coverage premises
remain analytic inputs, supported by the detailed written proofs and independent
mathematical reviews. This is not a fully formal theorem from RH alone.

The new box average gives the actual-ψ profile
`[v²+2(log 2)v+1.4175+L]/(2π)+.14`, with `L=log x`, `v=L/2−log L`,
on the complete real ray x≥e³⁵. Its complete function improves the original B5
profile by more than .546. That comparison is an unconditional kernel theorem
about the bound functions. Averaged explicit-formula and zero-density estimates,
and three exact Mellin/Stieltjes analytic identities, still appear as mathematical
inputs to the actual-ψ theorem. There is no extension of this ψ theorem to e²⁴;
the earlier e²⁴ threshold belongs to the separate direct-prime-window argument.

The absolute box Mellin identity removes oscillatory numerical integration:
its first regularized absolute moment is exactly log 2, while the second can be
bounded using 128 finite logarithmic terms instead of 128,000 quadrature cells.
The analytic derivation is in [BOX_MELLIN_EXACT.md](BOX_MELLIN_EXACT.md).
Unconditional new Lean lemmas prove the finite Mangoldt/log Abel identity, an
accelerated harmonic lower bound for the actual Euler constant, and summability
of the remaining positive logarithmic series.

No optimality or best-known-result claim is made. The count/width frontier is
not uniformly stronger than the optimized low-count/existence literature.

## What is source-first PV here

The executable source is the **unchanged** existing
`Solutions/RamanujanSourcePV.v1/c/verified_finite_log.c`, SHA256
`a22ee045b69b971a6fd3156ba745b3bebf7109ed98db43bf0064244e538b246c`.
It contains `rpc_log_ceildiv`, `rpc_log_series_upper`, and `rpc_log_upper`.
The new workload calls `rpc_log_upper` on every integer from 2 through 128:
127 actual nontrivial C calls; the 128-term sum also includes the exact log 1=0.

The existing verified infrastructure proves exact source-byte/AST-renderer
correspondence, unsigned 64/128-bit arithmetic and range safety, full source
execution of helpers and loops, termination, and the returned mathematical
integer model. `CLogMathLower.lean` strengthens the required finite-domain
accuracy with a proved lower enclosure, rather than subtracting a guessed
error from an upper output. `CLogSource.lean` connects that accuracy to actual
C source executions. `CLogNativeRows.lean` matches **every** actual returned
word to the proved source model and supplies its two-sided real-log interval.

`CLogMoment.lean` consumes those source-derived intervals in an exact kernel
aggregation, proving an upper expression below 567/800. Its actual C-derived
upper expression is approximately .708744640424; the discarded positive series
tail has the correct inequality direction. `CLogMomentNetwork.lean` supplies the
existing `RHSmoothingInputs.v1.box_moments` conclusion from the three precise
`BoxMellinInputs.v1` analytic claims. The existing network then propagates this
moment into actual ψ, LCM and primorial consumers. Its `box_psi` theorem also
composes the complete source-derived moment directly into the actual canonical
ψ conclusion, with no numerical-moment premise. The final replay compiles the
canonical `RHSmoothingInputs.v1/Solution.lean` challenge wrapper as well.

This is **source-first PV of the C logarithm component, followed by kernel
aggregation and conditional analytic consumers**. It does not verify the Python
harness, the entire Python quadrature, the analytic Mellin proof, or every
numerical program in IEANTN. Native C runs alone and ordinary certificate checks
are not called PV. There are no native execution axioms in the selected new final
proofs; their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Remaining execution trust is explicit: the Lean kernel and pinned generic
libraries; the documented restricted-C renderer/semantics relationship to GNU C;
correct GCC 11 compilation, unsigned integer/ABI behavior, runtime, OS and
hardware; and the Python/ctypes build/run association harness. The source proof
constructs successful executions rather than assuming a correct returned answer.
The actual returned words are independently matched by kernel proofs.

## Reproduce from a clean application build

From the repository root, run:

```sh
python Solutions/RHContinuation.v1/parabolic/reproduce_clog.py \
  --out /data/your-fresh-owned-output
```

The output directory must not exist. This script regenerates the native C data,
checks the actual native and directed numerical CLIs in normal, `-O` and `-OO`
modes, rejects invalid CLI routes, and rebuilds the complete final source closure
from the checkout. **No prebuilt application `.olean` is used.** Only the exact
compiler and generic dependency caches specified in
`../scripts/GENERIC_CONTEXT.json` may be reused. Their compiler hash and Git
commits are checked. To use different installation paths with the same pinned identities, run:

```sh
python Solutions/RHContinuation.v1/ramanujan/configure_context.py \
  --packages /your/pinned/generic/packages \
  --compiler /your/pinned/lean/bin/lean --out /data/fresh-context.json
IEANTN_GENERIC_CONTEXT=/data/fresh-context.json \
  python Solutions/RHContinuation.v1/parabolic/reproduce_clog.py \
  --out /data/your-fresh-owned-output
```

The helper checks the compiler SHA256 and every dependency commit. The environment
map was exercised by the final current-source replay. No network download or
package update occurs inside the experiment.

The run preserves commands, source hashes, native compiler/binary hashes, exact
outputs, all-mode receipts, resource logs, full application source closure,
compiler diagnostics and axiom audit. `RESULT.json` is published atomically only
after every active route and the complete final theorem pass. Failure leaves
partial evidence and no passing final receipt. The independent `validate_clog.py`
CLI checks the actual final theorem and canonical challenge wrapper, every source
identity, all nine child routes and their 27 rejected invalid routes. Its acceptance
and rejection paths are exercised in normal, `-O` and `-OO` modes. All acceptance
checks use explicit
errors and remain active under Python optimization. No random seeds are used.

Other deterministic track replays are:

```sh
python Solutions/RHContinuation.v1/parabolic/reproduce_track.py \
  --out /data/your-fresh-quartic-sextic-box-output \
  --core-library /data/your-fresh-owned-output/objects
python Solutions/RHContinuation.v1/parabolic/reproduce_octic.py \
  --out /data/your-fresh-octic-output \
  --core-library /data/your-fresh-owned-output/objects
python Solutions/RHContinuation.v1/parabolic/compile_stage.py \
  --out /data/your-fresh-Abel-output \
  --lib /data/your-fresh-owned-output/objects FiniteMangoldtAbel
```

The shared object directory in these commands is the explicitly fresh source
replay above, never an old experiment's application cache. Generic package
provisioning is documented by the exact version/commit manifest.

## Resources, retained evidence, and gaps

The C-source byte/AST binder needs more memory than ordinary proof modules.
The reproducer admits it with a 48 GiB address-space cap and uses 16 GiB for
other modules, while checking a 512 GiB host reserve before each job. These are
workload-specific caps, not the obsolete 4 GiB restriction. Actual measured
resident peaks and elapsed times are recorded independently. It never infers
available RAM from free disk space.

The native logarithm data and moment certificates are tiny. There are no generated
prime lists, enormous arrays, or large certificates to retain. Essential source,
exact parameters, output hashes, proof-source closure, and concise evidence must
be preserved; compiled caches can be regenerated. No unrelated directory or
historical input has been deleted. Failed attempts and corrected semantics are
recorded under the experiment data directory, separately from final acceptance.

`CLAIMS_AND_GAPS.json` lists every main result and its remaining mathematical
premises. `reviews/CORE_CONSUMER_REVIEW.json` independently checks the eleven
parent-authored actual network-consumer contracts. The octic independent
mathematical review and source check are preserved in `reviews/octic-independent/`.
These reviews do not claim an exhaustive source audit of all transitive historical analytic lemmas. The external zero-count
source is Brent–Platt–Trudgian, *The mean square of the error term in the prime
number theorem*, Journal of Number Theory 238 (2022), 740–762, Corollary 1 on
published page 743 ([arXiv2008.06140v1, PDF page4](https://arxiv.org/pdf/2008.06140v1#page=4)). The same authors’ *Accurate
estimation of sums over zeros of the Riemann zeta-function* is a different paper:
Mathematics of Computation 90 (2021), 2923–2935, arXiv2009.13791v1; its
[PDF page2 footnote1](https://arxiv.org/pdf/2009.13791v1#page=2) cites the former
for A=.28. Both primary versions print the domain T>=2pi; our proof uses only
the cutoff A=12>2pi and above, so the endpoint is not used. The opposite 7/8 sign printed
in Lee–Nosal Eq8 is a previously audited source typo and is not used here.

The documentary source correction and expanded residue/averaging justification
are recorded in `SOURCE_CORRECTION.json`. Archived pre-correction documents are
retained separately; all Lean, C, numerical parameters, receipts and mathematical
bounds are unchanged.
