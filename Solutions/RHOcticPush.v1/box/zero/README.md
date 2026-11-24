# Actual Box zero-estimate continuation

This directory proves the existing, unchanged
`RHSmoothingInputs.v1.box_zero_estimate`. The exact original predicate is closed
in Lean development builds, with only the general published Nicolas and BPT
inputs explicit. No moment, pointwise-packet or desired zero-estimate premise
remains. Actual full zero-packet summability is also proved for every real L >=35
and every real s <=1. Final independent fresh source closure and canonical node
integration are separate acceptance gates; see `FINAL_ZERO_SOURCE_FREEZE.json`.

The actual objects are `IEANTN.RHSmoothing.zeroPacket`, `zeroAverage`, `box`,
`delta`, `v`, `J`, and `IEANTN.zetaOrder`. No finite zero sample replaces the
infinite zero sum. The goal includes all real logarithms L >= 35, both s = -1
and s = 1, the original multiplicities, and the original additive allowance0.131.

The accepted analytic proof has these parts:

- `BoxEndpointBPT` and `BoxEndpointInfinite`: exact lower-endpoint BPT transport,
  a smooth approximation of the absolute value, actual infinite summability,
  and the exact remainder at height12. The actual zero count at12 is proved0.
- `BoxZeroKernel`: the actual Fourier transform F(y) = sinc(y), its actual
  derivative D, bounds abs(D(y)) <= abs(y)/3 and <=2/y for positivey, and a
  complete positive-zero BPT specialization of f(t) = F(delta*t)/t.
- `BoxQuadraticTail` and `BoxPositivePieces`: the entire reciprocal-square zero
  tail above32768 and the finite multiplicity count up to32768. The bounds
  <=1/20000 and <=40000 follow from BPT and proved scalar inequalities. No zero
  table or height-truncation premise is used.
- `BoxDerivativeTransport`: the complete derivative integral splits at32768;
  its tail is integrated analytically. The baseline is1/t^2, with the actual
  sinc-derivative correction retained separately.
- `BoxZeroMoments` and `BoxScaledMoments`: the singular baseline is integrated
  exactly; the entire interval from0 to12*delta remains in the proof. This
  retains the negative cutoff constant and costs at most4*delta^2. Both actual
  regularized moments, including the logarithmic moment, occur without a moment
  hypothesis. The scale identity is exactly the original v(L).
- `BoxUnshiftedBound`: the complete unshifted positive-zero sum is bounded by
  the actual moment polynomial plus the exact endpoint, derivative and small
  interval allowances.
- `BoxZeroPairing` and `BoxTransportMajorant`: genuine whole-family summability,
  exact conjugate pairing, real-axis/low-height order exclusion, and the actual
  piecewise low/high majorant. A complex pointwise packet bound is lifted to
  the entire sum only after the required summability has been proved.
- `BoxZeroInflation`: a pure analytic inequality controls the exponential
  multiplier; this is not a new numerical certificate.

`FINAL_ZERO_SOURCE_FREEZE.json` records all18 new zero-proof sources, exact hashes,
accepted commands, banks, wall times, peak RSS and46 printed proof-root axiom
checks. All46 roots use only propext, Classical.choice and Quot.sound. Accepted
source bytes are frozen. The historical twelve-source checkpoint is preserved.
Scalar, complex-shift, source normalization and signed packet bounds have
independent read-only reviews. The final consumer is `BoxZeroEstimate.lean`.

The remaining general literature inputs are the actual BPT zero-count bound
and, in the reused low-height/real-axis exclusion and full-family bridge, the
Nicolas spectral identity. The BPT off-ordinate source predicate has a proved
right-limit adapter to the exact closed-count convention. These inputs remain
visible hypotheses. This checkpoint is not an RH-only theorem, a proof of a
published analytic source, or a source-first PV result. It is ordinary Lean
kernel mathematics. In particular, the kernel-certified scalar checks are not
called PV.

## Verification and reproduction

Each evidence directory contains the exact accepted development command and
source hash. For example, from the network checkout:

```
python3 Solutions/RHOcticPush.v1/scripts/dev_compile.py \
  --source Solutions/RHOcticPush.v1/box/zero/BoxZeroInflation.lean \
  --out /absolute/fresh/output
```

For modules with application imports, supply the exact banks listed in their
receipts using repeated `--bank` arguments. This command is explicitly a
**development check**, not a clean-environment acceptance receipt. It uses the
pinned Lean4.34.0-rc2 toolchain, two Lean threads, and a64GiB per-job limit.

The parent integration reproducer must capture every required original and new
application source, compile the complete dependency graph from source in a fresh
isolated namespace, audit the final proof roots, and reproduce the unchanged
canonical consumer. It must not accept this development bank as a substitute
for that final fresh closure. The final evidence bundle and central report own
that separate acceptance gate.

No large data set is generated here. Source code, original papers, exact
receipts and accepted proof artifacts are retained. Failed proof drafts were
rejected and are recorded in `ATTEMPTS.md`; they are not accepted outcomes.

## Independent fresh source replay

The independent replay in `evidence/cold40-v1/RESULT.json` passed: exactly40
frozen new scientific modules (Gamma10, derivative8, Stieltjes4, zero18) and
one generated exact-consumer/audit module were compiled in a fresh isolated
namespace above the recursively validated source-fresh619 campaign foundation.
That makes660 scoped source files including audit modules; the619 foundation
was validated and reused, not falsely counted as freshly recompiled here.
All381 theorem declarations owned by the40 scientific modules have only
`propext`, `Classical.choice`, and `Quot.sound`. All41 actual dependency probes
were checked against pinned generic libraries or exact source-fresh objects.
No developer application objects or historical application cache entered.

The41 fresh compilations and probes took507.366seconds. GNU time recorded
a maximum child RSS of8,282,232KiB; sampled controller-tree RSS peaked at
8,535,179,264bytes. Owned disk before final receipt was13,958,539bytes.
All owned processes returned0; no owned-process OOM was observed. Samples
are not exact continuous aggregate RAM or disk high-water marks.

From the repository root, using a completed source-fresh619 campaign run:

```
python3 Solutions/RHOcticPush.v1/box/zero/reproduce_zero.py \
  --foundation /absolute/source-fresh619-run \
  --out /absolute/new-owned-output
python3 Solutions/RHOcticPush.v1/box/zero/reproduce_zero.py \
  --verify /absolute/new-owned-output
python3 Solutions/RHOcticPush.v1/box/zero/controls_zero.py \
  --run /absolute/new-owned-output --out /absolute/new-owned-controls
```

The exact source capture is `cold-capture/SOURCE_CLOSURE.json`. Regeneration
uses `prepare_cold.py` and rejects an existing capture rather than overwriting
historical evidence. For a clean machine, first reproduce the pinned generic
context and the complete619 pipeline documented in the integration README;
`--foundation` validates that entire source/compile/run receipt chain before
any reuse. The new run admits one2-thread64GiB job only if available RAM
also preserves512GiB for the host. Free disk is checked independently.
Normal, `-O`, `-OO`, adversarial-mutation and relocation controls are recorded
in a separate study; see its actual final receipt before claiming completion.

This is ordinary kernel verification of mathematics. Genuine general Nicolas
and BPT source assumptions remain visible; it is not source-first PV or an
RH-only proof of those literature inputs. The independent Perron source/final
adapter reviews are in `PERRON_*_INDEPENDENT_REVIEW.json`.

All19 actual CLI controls have now passed: valid readback plus source/object/foreign-import/nonstandard-axiom/duplicate-JSON rejection in normal, -O and -OO modes, and a relocated valid copy. Exact receipts and mutation evidence are retained in `evidence/cold40-controls-v1/`. Duplicated regenerable control object banks were deleted only after scope checks; accepted proofs were retained. `reproduce_from_clean.py --out /absolute/new-directory` composes all source stages and controls after pinned generic bootstrap; that new wrapper has not itself been run as a second entire660-source campaign. Its component routes are the independently executed source-fresh campaign.
