# Actual Gamma–Mellin reconstruction and first Box moment

This additive study preserves every earlier octic and Box source. The actual
canonical `BoxMellinInputs.v1.first_moment` is now proved by the no-argument
`RHOcticPush.BoxGamma.first_moment` in `BoxFirstMoment.lean`. It includes actual
integrability and J(box,0)=log2. No RH, source theorem, moment identity, numerical
certificate or generated output is a parameter of that theorem. Ordinary Lean
kernel proofs use only propext, Classical.choice and Quot.sound. This is not
source-first program verification of C/C++/CUDA.

## Mathematical chain

1. `GammaEuler`: explicit rational Jacobian x/(1−x), actual Beta integral and
   existing Gamma reflection prove the complete Euler integral on0..∞.
2. `GammaQuadratic`: actual t² substitution proves the complete rational integral
   ∫t^(−s)/(1+t²)dt=π/(2cos(πs/2)) and its genuine integrability.
3. `GammaDamped`: actual complex exponential integral proves the real positive
   Laplace kernel ∫(1−cosy)exp(−ty)dy=1/[t(1+t²)], all t>0.
4. `GammaMellin`: full product integrability and justified Fubini, plus the actual
   Gamma Laplace integral, prove ∫(1−cosy)y^(s−2)dy=π/[2Γ(2−s)cos(πs/2)] for
   every real0<s<1. Actual integrability is proved separately.
5. `GammaScaling` and `GammaBoxSeries`: exact positive scaling evaluates every
   actual BoxPositiveMellin term and consumes the full-strip infinite-series/
   integral exchange to obtain the actual complete Box Mellin series.
6. `BoxHSeries`: the convergent correction H(s)=Σn≥1 n^(−1−s)/(4n²−1) is
   continuous at0, and H(0)=2log2−1 follows from a proved exact finite harmonic
   identity and genuine harmonic asymptotics.
7. `BoxFactorization`: actual M(s)=P(s)[ζ(1+s)+H(s)], with actual P(s)=
   2^(−s)/[Γ(2−s)cos(πs/2)]. Both the real series and actual complex zeta are linked.
8. `BoxFirstMoment`: actual Mathlib zeta finite partγ, Root's independently
   proved P′(0)=1−γ−log2, and the independent actual Mellin coefficient extraction
   give the original complete first-moment predicate.
9. `BoxHDerivative`: actual infinite differentiation proves H′(0)=−q, where q
   is the original canonical convergent logarithmic series, including exact
   n0/n1 exclusions. It supplies a genuine input for the remaining J1 assembly.

The generic Gamma identity was derived by positive Laplace/Fubini rather than
assuming a complex boundary-value Gamma transform. No condition at infinity was
replaced by a finite numerical cutoff. No new mathematical axiom or sorry occurs.
The first-moment proof needs no externally unformalized analytic source theorem.
The full Box explicit formula, full Box zero estimate and second-moment identity
remain distinct open predicates at this saved stage; consult the latest integrated
report for later completed work.

## Exact scope and frozen evidence

`SOURCE_FREEZE.json` preserves the first four sources. `FIRST_MOMENT_SOURCE_FREEZE.json`
pins five later sources, including the complete first moment. `H_DERIVATIVE_SOURCE_FREEZE.json`
pins the tenth source. All accepted receipts/stdout/GNUtime logs are under evidence/.
Rejected development attempts remain recorded in ATTEMPTS.md and owned scratch.
The Root-owned scalar derivative sources have independent read-only reviews in
ROOT_DERIVATIVES_INDEPENDENT_REVIEW.json and its V2 extension.

The separate `../stieltjes/StieltjesDerivative.lean` proves actual differentiation
of Mathlib's termTSum at1, using dominated parameter differentiation and a full
summable4n^(−3/2) derivative bound on s>3/4. Its exact freeze/receipts live there;
the other worker owns the canonical Stieltjes/regular-zeta identification.

## Reproduce

Pinned Lean4.34.0-rc2 and Mathlib71a80585ee495fc24472fd0eaffc89d94e4fd8d6 are required.
The complete canonical first-moment proof must be reproduced by the study's
source-only integration controller with a current manifest containing all ten
Gamma sources and their actual application dependencies. The developer receipts
reuse disclosed application objects and do not establish that final fresh gate.

The five generic Gamma/scaling files have an additional small clean source replay,
with **no application object banks**. From the network root:

```sh
python3 Solutions/RHOcticPush.v1/box/gamma/reproduce_generic.py --out /data/FRESH_GAMMA
```

The default generic-context JSON records exact installed compiler/dependency
locations. For a clean environment, install the pinned toolchain and dependencies,
then pass `--context` with their local locations; compiler bytes, commits and
tracked-source cleanliness are checked. `--check` runs preflight without compiling.
The full five-file replay passed under Python-OO; positive and wrong-revision
preflight controls passed in normal, -O and -OO modes. Acceptance uses explicit
errors and never assert/__debug__. Fresh receipts are published only after all
five compilations, exact source hashes and printed axiom sets pass.

## Resources and storage

All development and the bounded fresh generic runs admit64GiB per compiler job,
use two threads and retain measured time/peak RAM in receipts. No numerical data,
random seeds, prime lists or large arrays are generated. This subexperiment uses
small source/proof/log artifacts; no large regenerable data required cleanup.
Accepted proof artifacts and original sources remain preserved. Compiler, runtime,
OS and hardware remain trusted. No new external numerical program was verified.
