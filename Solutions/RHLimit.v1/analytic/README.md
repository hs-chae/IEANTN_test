# Analytic proof closures for RHLimit

This directory contains five new Lean modules, with no new axioms, `sorry`,
`native_decide`, numerical outputs assumed as mathematical facts, or changes to
historical RHContinuation results. These are ordinary kernel proofs. The new
Stieltjes result also removes one analytic input from the existing actual C-log
program → moment bounds → PNT consumer. Only that reused, separately documented
C execution component has source-first PV status; none of the new calculus proofs
is relabeled PV, and the whole analytic PNT pipeline is not claimed source-first PV.

## What is proved

- `StieltjesTrapezoid.lean`: the actual sequence
  Sₙ = Σ₂≤k≤n log(k)/k − log²(n)/2 converges to the existing `limUnder`
  definition of γ₁, and S₁₂₈ − log(128)/256 ≤ γ₁. The proof uses convexity of
  log(t)/t on t ≥ 128 and exact integral/trapezoid estimates. It does not identify
  γ₁ with the zeta Laurent coefficient; that belongs to the remaining Mellin identity.
- `BoxMomentReduced.lean`: the unchanged actual C-source log/moment numerical
  chain yields the actual `RHSmoothing.v1.box_psi` from RH and **four** analytic
  propositions, replacing the previous five. The removed premise is precisely
  `BoxMellinInputs.v1.stieltjes_trapezoid`.
- `OcticFourier.lean`: the actual `EvenKernel.transform 4` kernel integral equals
  the exact eight-term rational/trigonometric expression used by the numerical
  work for every nonzero argument; its value at zero is 16/9. The actual derivative
  equals the exact nine-term derivative expression. No out-of-domain equality at
  zero is asserted for the rational expression.
- `BPTZeroCount.lean`: the precise **literature-backed input** below implies the
  actual closed zero count N(12) = 0. Also proved: the finite weighted RvM
  remainder identity and its C1 absolute-error estimate.
- `AbsoluteStieltjes.lean`: the finite absolute-value zero estimate follows for
  every C1 real function without assuming that its absolute value is C1.
  Smooth majorants √(f² + ε²), their derivative bounds, finite zero multiplicities,
  and ε → 0 are all proved. `octic_finite_bound` applies this to the actual scaled
  octic kernel δ·transform₄(δt), δ > 0, with its proved derivative.

All final roots audited in the receipts depend only on `propext`,
`Classical.choice`, and `Quot.sound` as Lean axioms. Explicit propositions in a
conditional theorem's type remain mathematical inputs; this axiom audit does not
pretend to prove those inputs.

## Exact source input and scope

`PublishedBound` states, for every T ≥ 2π,

|N(T) − [T log(T/(2π))/(2π) − T/(2π) + 7/8]| ≤ (7/25) log(T).

Here N is the actual `ZeroCount.v1.zetaNClosed`, counting 0 < Im(ρ) ≤ T with
multiplicity. The source is Brent–Platt–Trudgian, *The mean square of the error
term in the prime number theorem*, J. Number Theory 238 (2022), 740–762,
**Corollary 1, p.743**, [arXiv:2008.06140v1, PDF p.4](https://arxiv.org/pdf/2008.06140v1#page=4).
The same primary source's Lemma 2, PDF p.5, displays the finite sum convention
T₁ < γ ≤ T₂. Corollary 1's low-height proof uses a published interval computation
up to 1.03·10⁸; this project has **not** independently verified that computation.
The input is explicit and remains literature-backed.

No new standalone Blueprint label has been registered by these helper modules.
The count definition and its existing Blueprint correspondence are in
`IEANTN/Nodes/ZeroCount/v1/Conclusions.lean`; the original imported node records
CH2 Appendix B Lemma B.1, whose weaker bound is deliberately **not** substituted
for BPT's bound here. `IEANTN.HasRvMBound` has a different fixed threshold and
an open counting interval, so it is not silently reused.

The finite estimate, with M′(t) = log(t/(2π))/(2π), is

Σₐ<γ≤b |f(γ)| ≤ ∫ₐᵇ |f(t)|M′(t) dt
  + (7/25)[|f(b)|log(b) + |f(a)|log(a) + ∫ₐᵇ |f′(t)|log(t) dt],

for 2π ≤ a ≤ b. This is derived here; the source is the published zero-count
bound, not a claim that the paper directly states this exact nonmonotone formula.

This is a focused audit of the newly introduced analytic interfaces and their
actual imported definitions. It is not an exhaustive source audit of every
externally attributed declaration in the reused 46- or 111-source closure.

## Reproduce from a clean application source tree

Use the pinned Lean 4.34.0-rc2 binary and generic dependency revisions listed in
`Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json`. That file pins the
compiler SHA-256 and nine generic source commits, including Mathlib
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. Generic library setup/transport is
separate from application proof replay; see the existing
`Solutions/RHContinuation.v1/README.md` and its bundle bootstrap instructions.
`IEANTN_GENERIC_CONTEXT=/absolute/relocated.json` may relocate those exact
identities. It does not authorize changing the pinned compiler or source commits.
Python 3 and GNU `/usr/bin/time` are required; the reused C-log reproducer also
uses the original documented C toolchain. All computations are deterministic;
there are no random seeds.

From the `network` root, with fresh experiment-owned output paths:

```sh
python3 Solutions/RHLimit.v1/analytic/reproduce.py --out /scratch/rh-box48
python3 Solutions/RHLimit.v1/analytic/reproduce_absolute.py --out /scratch/rh-absolute114
python3 Solutions/RHLimit.v1/analytic/controls.py --out /scratch/rh-controls48 --base-run /scratch/rh-box48/baseline
```

The first command rebuilds all 46 actual old C-log/moment/PNT source modules and
both new Stieltjes/reduced-consumer modules. It regenerates the original log and
moment numerical routes, uses the original checkers, and prints the final theorem
axiom audits. The second command rebuilds all 111 exact original frozen integrated
sources, then Fourier, BPT, and absolute-Stieltjes bridges. No prebuilt application
objects enter either default route. `reproduce_common.py` alone creates the
111+2 intermediate bank. Every new/common Lean compile is actually `-j8` with an
80 GiB address-space cap; the original unchanged C-log replay retains its recorded
per-module caps, all above the obsolete 4 GiB restriction where required.

For an already completed **newly created** bank, the equivalent composed route is:

```sh
python3 Solutions/RHLimit.v1/analytic/reproduce_common.py --out /scratch/rh-common113
python3 Solutions/RHLimit.v1/analytic/reproduce_absolute.py --out /scratch/rh-absolute-append --base-run /scratch/rh-common113
```

Run the matching all-mode controls after the composed route:

```sh
python3 Solutions/RHLimit.v1/analytic/controls_absolute.py --out /scratch/rh-controls114 --base-run /scratch/rh-common113
```

The append validates every source/object hash, all 113 actual successful build
records, compiler, source manifest and executed controller identity. A historical
unbound application cache is not accepted. `reproduce.py --base-run` likewise
accepts only the 46-source bank whose object-binding receipt this controller wrote
after its actual fresh run. `--check` means source/compiler/dependency preflight
only; it is never reported as a Lean proof replay.

Controllers use explicit validation errors, strict duplicate/nonfinite JSON
parsing, fresh output directories, exact theorem identities and axiom sets, and
atomic final receipts. They do not use `assert` or `__debug__` for acceptance.
The 48-route controls execute actual positive/negative CLIs in normal, `-O`, and
`-OO` Python modes. Common/absolute controls and actual replay receipts are retained
with the evidence. A rejected, interrupted, or partial run does not receive a PASS
receipt.

## Remaining mathematical obligations and trust

The reduced box PNT theorem still assumes RH, the averaged explicit formula,
its zero estimate, the first Mellin identity, and the second Mellin identity.
The four named analytic propositions remain explicit; RH is separately explicit.
This does not turn the entire pointwise PNT bound into an unconditional kernel theorem.

For the octic bound, the full actual smoothed explicit formula and infinite
zero-estimate contract remain open. The finite absolute-value/derivative bridge
is now proved, but the infinite-tail passage, signed/all-zero series attachment,
and formal integral caps for the actual A/B and derivative moments still need
proofs. Existing exploratory rational moment computations are not promoted to
verified facts, are not PV, and are not imported as hidden numerical premises.

The new proofs trust the pinned Lean kernel/compiler, its generic library objects
under the existing generic-library boundary, runtime, OS/filesystem execution and
hardware. The reused documented C numerical component additionally retains its
original C compiler/runtime/hardware boundary. Published BPT and the other explicit
analytic propositions are mathematical source inputs, not generic platform facts.
LSP diagnostics were attempted first but the ordinary workspace server could not
resolve the isolated generated module paths (or returned partial elaboration);
actual pinned direct-compiler source replays are the proof evidence.

Only owned regenerable temporary files may be removed after successful replay.
Keep source, exact manifests, commands, logs, receipts and accepted proof artifacts.
No original paper, locked input, historical result or unrelated workspace is deleted.
