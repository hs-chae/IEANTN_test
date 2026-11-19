# Factual work and limitation notes

- Inputs: /task/INPUT_CONTRACT.json (A-D01); conventions and admitted
  trust labels as in /task/{COMMON_FOUNDATION,BASELINES,EVALUATION_RULES}.md;
  source versions in SOURCE_INDEX.json, all from /corpus/originals per
  RUNTIME_PATHS.json. No work delegated and no external web/data used.
  PDF page numbers follow the packet's original-page markers.
- Checkpoint at 25%: density and spectral-tail designs, initial
  Ramanujan/Mertens candidates and comparisons. At 50%: first SHA lock,
  all-real Ramanujan certification, and completed finite sieve replay.
  At 75%: preserved a complete consistent lock before extending it with
  short intervals, exact local roots, and a density-free fallback.
  Post-75 tests and revisions were made within the same research budget.
- Status: new study's deductions from admitted assumptions/results
  (supported_argument) and ordinary exact computation certificates.
  Neither a trained numerical guess, a new literature input, a kernel
  proof, nor source-first proof verification is claimed. The historical
  integer segment still relies on the original Ramanujan computation.
  Finite-RH verification is admitted from Platt–Trudgian FiniteRH Thm 1,
  not rerun. Likewise CH2 Lemma 9.2 uses its stated psi extrema, and we
  do not rely on the potentially ambiguous weighted display (9.1).
- FKS Cor. 2.9/Table 8 is used with its literal tabulated conclusion.
  Do not substitute its printed delta column blindly into Thm 2.7
  (printed hypothesis delta>=1 versus Table 8 values below 1).
  H-only and S density-free bridges and the Mertens tolerance gains
  do not need that table. FKS Theorem 3.2 is used with the admissible
  sample constants in the source, not the more problematic version in
  Theorem 3.1 (see FKS Remark 3.3).
- Ramanujan baseline endpoint: computed the last local prime counts by
  floor-quotient sieve, rather than assuming the published all-real
  text agrees with the integer computation. Independent small test
  compares pi(n) to trial division for n<=1000; the large counts and
  all bracket assertions passed. Near the real root no approximation
  such as replacing x/e by a rounded float is used.
- Exact sieve: normal and GCC undefined-behavior-sanitized runs passed
  on 10^8, enumerating 5,761,455 primes. Sanitized build flags
  -fsanitize=undefined -fno-sanitize-recover=undefined supplement (not
  replace) the directed-integer/algorithmic argument. Scalar Python
  checks passed: bridges on closed 1/50 log cells, all endpoint
  brackets, analytic tail comparisons, and short intervals. Binary,
  raw logs, scratch exploration and all source data need not be
  submitted. Fraction/interval diagnostics may print decimal
  approximations but never decide a certificate assertion.
- Unsuccessful / dominated routes: a direct use of H at log x=200
  incurs L^4 times the normalized pi error in the Ramanujan gap
  (not small there); CH2 supplies the medium-scale bridge. Truncating
  the factorial li expansion without a boundary anchor is not a
  rigorous remainder estimate. Treating the Mertens integral by a
  pointwise absolute theta bound alone costs extra size and does not
  certify a positive sign on the moderate interval. An early proposed
  uniform .19850/L^3 log-product improvement at x=2278382 failed
  on the gap 2278379..2278421; the sharp local threshold explains why.
  An attempted .299/L^2 at 912560 fails similarly; the smaller 912565
  improvement is separately certified. Arithmetic bounds up to
  10^8 first explored using floating scans were not reported as
  theorems; the published diagonal rows were replayed using exact
  dyadic enclosures including left limits.
- Limits: no proof that the Mertens sign extends past 10^13, no new
  table of zeros, no optimality claim for analytic constants or
  short-interval exponents, and no independent reproduction of the
  claimed original source computations beyond the identified local
  endpoint. The theorem-status distinction for S is explicit:
  accepting the supplied QRH theorem removes H but not the dependence
  on that original theorem; H gives S directly via analytic continuation.
