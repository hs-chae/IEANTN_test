# Posthoc proof of the prospective degree56 witness

This folder preserves and verifies the new polynomial discovered in the frozen
E2 trial `functional-L2_E2_V0-r1`, timely prefix `prefix-0001`, at 17,916 tokens
before its 18,000-token limit. The primary trial's written/numerical outcome
remains unchanged. This subsequent Lean proof work is **posthoc verification**,
not a retroactive primary Lean success or a controlled new exposure trial.

`OPT28_ORIGINAL.json` contains the original 29 rational coefficients of P(y²),
where y = √π x. Its SHA-256 is
`1a396b22abfb3827d3d8018787c37608379252b049ddcde8bd924a3b6d8b3b1a`.
`CANDIDATE_LAGUERRE28.json` is the exact triangular change of basis to 29
Laguerre coefficients, with zero residual. Its different SHA-256 is
`057330776a0aedb31bbf455fdbf611012e41ebd3eb35b77b47d07fb7e9fb2656`.
The physical polynomial has degree56. Both input identities are retained.

An independent, unchanged predecessor exact-Sturm and directed-Arb checker
verified the complete infinite Gaussian integrals in 11.886 seconds at 256 bits,
without using the trial model's checker. Its inverse quotient enclosure is
0.8339454456523582342797504018125673513 ± 2.17×10⁻³⁸.
The exact original P and its Fourier polynomial Q were independently associated
using the monomial/Hermite recurrence. These are externally trusted numerical
results, not Lean proofs or source-first PV.

The additive Lean fork reuses the unchanged generic `G40Cell` through `G40Rays`
proofs. Those proofs support every polynomial with at most81 coefficients,
which includes this actual 57-position pair. No old actual Gaussian numerical
witness or numerical-bound premise is reused. The new actual functions are
`RH080.Gaussian28.physicalF/G`, evaluated using the shared generic coefficient
function at √π x and multiplied by exp(−π x²). Their actual Fourier association
is supplied by the separate `primal56_fourier` lane.

The fixed finite partition has 579 norm cells and 556 positive-wing cells,
1,135 in total, emitted into 24 source modules. Parameters are mesh denominator32,
root refinement denominator1,048,576, polynomial Taylor order8, exponential
Taylor order24, 256-bit upward exponential rounding and 80-bit upward cell
rounding. The radial cutoff is12; the full infinite tails are separately bounded.
No randomness is used. Generation itself is not mathematical acceptance: every
cell validity proposition and the generic integral theorem must pass the kernel.

The targeted proved budgets are mass≤0.7484161247, exterior positive Fourier
leakage≤0.0313377324, and the exact equality F(0)=1. At A=36/11 these give
82325773717/98718416336 = 0.8339454457696559…, strictly below the original timely
trial's stated upper bound0.833945448. Consult the final numerical receipt and
the sibling v3 source-only joint replay for actual completed proof status;
do not interpret this description or a generated cell as an accepted theorem.

## Reproduce

The certificate generator uses only Python's standard library. The actual
regeneration environment is Python3.11.14. From the repository root:

```sh
python3 Solutions/RH080Study.v1/functional/primal28/regenerate.py \
  --out /absolute/fresh/scratch/degree56-generation
```

The output must be outside the checkout. The script reconstructs exact P/Q,
checks association with the original timely polynomial, regenerates all24
cell sources and verifies every byte against the frozen manifest. Only after
all checks pass does it publish `REGENERATION_RECEIPT.json`. Normal, `-O` and
`-OO` routes are checked separately. This receipt proves deterministic source
reproduction, not Lean acceptance.

The final source-only v3 Fourier/numerical/CMS replay is maintained by the
sibling `primal56_gap` lane. It must recompile the new actual cells, all generic
proof dependencies, actual Fourier proof and final mathematical consumers;
ordinary cached predecessor numerical witnesses are not accepted substitutes.
The source/compiler/toolchain hashes, exact commands, per-process maximum RAM,
execution times and output hashes are recorded by that replay.

This is kernel-only numerical verification, **not source-first PV**. The
source-first C compact-dual program elsewhere in the study is separate. All
original degree80/v2 results and source bytes remain unchanged. The eventual
RH prime-gap and population consequences retain the existing general CMS
analytic source predicates and ordinary RH; no explicit onset, optimality,
global-record claim or0.8 conclusion follows.
