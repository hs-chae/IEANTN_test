# Bounded frontier and spectral supplement

Both unchanged parent-authored modules were independently replayed:

- `FrontierPoint.lean`: all eight axioms audits are exactly the standard three.
  Independent replay: 15.29 seconds, 4,918,596 KiB peak RSS.
- `SpectralBenchmark.lean`: the uniform strict gain above .540 has exactly the
  standard three axioms. Independent replay: 2.62 seconds.

The first independent frontier attempt used a 16 GiB address-space cap and `-j1`;
it aborted with a thread-creation allocation exception (exit134). That is a
resource failure, not an unresolved theorem or an observed OOM kill. The same
source passed with a 48 GiB address-space cap. Its mathematical source was not
edited. The parent's independent v2 also passed in 16.73 seconds.

At L=100, the point module proves B*<355 and each of the six displayed comparator
functions exceeds355. It proves e100 exceeds the specified finite Buthe endpoint.
This is a point comparison among those formulas, not an all-point/global winner
or a fresh exhaustive audit of all their primary-source transcriptions. In
particular, the stronger finite Buthe rows remain relevant on their finite domain.

The spectral module compares B*+.2772/L with B5+.076/L for every L≥35. The latter
is the old written profile; this function comparison does not formalize or assume
its analytic transport theorem. The exact penalty difference is .2012/L, so the
already proved box gain above .546 leaves a strict gain above .540.

Both supplements are kernel mathematics, not source-first PV. They do not change
the five actual-box analytic premises, six octic prime-kernel contracts, or the
sealed 46-source C-log→actual-ψ proof/evidence.

## Minimal replay using explicitly fresh source banks

Set `RH_CHECKERS` to the freshly source-rebuilt Ramanujan checker bank and
`RH_PNT` to the freshly source-rebuilt C-log or root PNT bank. Each bank must use
the pinned generic compiler/context. Historical application caches are excluded.
The following uses separate banks and avoids irrelevant overlapping modules.
Every output subdirectory must be fresh.

```sh
RH_REPO=/path/to/the/pinned/checkout
RH_CHECKERS=/path/to/fresh/Ramanujan/objects
RH_PNT=/path/to/fresh/PNT/objects
RH_OUT=/path/to/fresh/owned/supplement
mkdir -p "$RH_OUT"
(
  set -eu
  ulimit -v 50331648
  python "$RH_REPO/Solutions/RHContinuation.v1/scripts/build_modules.py" \
    --source "$RH_REPO" --out "$RH_OUT/core" \
    --extra-library "$RH_CHECKERS" --module IEANTN.Vocabulary.RHSmoothing
  python "$RH_REPO/Solutions/RHContinuation.v1/scripts/build_modules.py" \
    --source "$RH_REPO/Solutions/RHContinuation.v1/integration/source" \
    --out "$RH_OUT/frontier" --extra-library "$RH_OUT/core/objects" \
    --module FrontierPoint
  python "$RH_REPO/Solutions/RHContinuation.v1/scripts/build_modules.py" \
    --source "$RH_REPO/Solutions/RHContinuation.v1/integration/source" \
    --out "$RH_OUT/spectral" --extra-library "$RH_PNT" \
    --module SpectralBenchmark
)
```

`IEANTN_GENERIC_CONTEXT` supports the already tested portable dependency map.
The 48 GiB cap here is address space, not measured resident memory. Preserve the
build JSON, all diagnostics and axiom audits. No native executor is needed for
either mathematical statement.
