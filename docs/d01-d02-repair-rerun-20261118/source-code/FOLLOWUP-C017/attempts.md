# Substantive iterations, repairs, and remaining limitations

* Directly substituting D02 into partial summation pays the
  log^2 of the premise and a tail factor about 1/a. At its
  starting point u=200 the original CH2 bound on psi is
  actually smaller than that raw input. Merely comparing this
  substitution against an old inverse-log bound would miss the
  relevant incumbent. The holomorphic continuation deduction,
  real smoothing, common zero-density split and signed
  frequency primitive in this portfolio address this problem.
* A direct truncated Perron estimate using only a zero-free
  cap and the full reciprocal-zero sum produces a growing
  log factor. Partitioning high zeros by their real part
  (rather than treating the entire sum as if at the cap)
  yields a summable bound for the right-hand density and
  removes the factor. Adaptive box widths were tested for
  transition scales; fixed h=5e-13 and endpoint convexity
  extend the D02 power branch below 170, and the continuous
  density majorant improves the asymptotic constants beyond
  the fixed grid. There is no assertion the chosen window or
  density splitting is extremal.
* We did not rely on a questionable truncation constant:
  FKS p.8 Remark 3.3 explicitly flags errors in earlier
  formula proofs. Using the integrated classical formula and
  local L^2 convergence avoids reinstating that step. An
  apparent delta-parameter discrepancy between FKS Theorem
  2.7 and its displayed density calculation is not needed
  here: the numerical density proof uses Dusart's explicit
  Theorem 2.3 and written elementary bounds instead.
* The first attempted low-frequency constant 114 failed the
  exact FKS reciprocal-sum check (the actual upper estimate
  in that calculation is about 115.0613). The final 116 is
  checked. Fixed factorial projections also have negative
  coefficients beyond the retained order; assertions of
  positivity at every power fail. The proof absorbs the
  negative coefficients in the tail penalty and verifies the
  derivative of the positive allowance. The simpler order-20
  truncation alone was unsatisfactory at order 20, which
  motivated the order-30 anchor and the full ideal profile.
  The finite CH2 minimizing-height choice has been clamped
  to its prescribed T>=10^7 and tested against x>max(T,10^9).
* Retaining only the first zero-free tail in the Ramanujan
  inequality would miss the early common finite pi window.
  Büthe's finite bound was joined with the CH2/spectral
  branches and a signed prime-power subtraction; at the
  finite cutoffs the exact cells use only eligible premises.
  The real endpoint was tested with exact prime counts since
  the known last failing integer does not determine the real
  onset. This revealed a concrete counterexample to the
  original strict real interval and necessitated a repair.
  Only the historical integer computation is used for the
  remaining low-range sign assertion; it was not rerun.
* Mertens finite constants were refined with a corrected
  trapezoid enclosure of gamma and a theta Stieltjes tail for
  the normalizers. An initial 10^7 range was insufficient
  for the .12 tradeoff. A 25-million sweep plus the new
  analytic joins supplies it, with independent root brackets
  near the original onsets. A separate signed U_0 transfer
  lowers the post-sweep coefficient to .10994 for the two
  products and the reciprocal sum, joining their .11 rows.
  The .10 sweep entries and the weighted .11 sweep entry
  did not follow on the earlier whole rays in the original run: the
  remaining gap is between the last checked prime slabs
  and the generic analytic coefficients after the sweep.
  Extending the finite verification or obtaining tighter
  one-sided psi information would close that gap.
  The finite li-transfer repairs the otherwise artificial
  loss where CH2's empirical psi range ends; we also retained
  the stronger arbitrary-sigma weighted CH2 transfer.
* These estimates do not absorb unproved cancellation of
  high zero phases, and neither zero-free assumption rules
  out zeros on its boundary. Sharper main-frequency
  information or actual one-sided weighted phase control
  would be necessary to assert a better power on this route.
  At fixed early arithmetic thresholds the binding inputs
  are the exact finite jumps or the common finite-height
  pi estimates, so D02 is not presented as a cause of those
  improvements. Some calculations use inherited literature
  tables and not fresh verification of zero locations.
  The original portfolio was independently assessed; see repair.md
  for the disposition of the findings and the continuation.
