# Original-source incidence and comparison scope

source_audit.py checks hashes of the 14 exact PDF/text objects
bound by the input contract. Locators here are **PDF page numbers**,
not journal pagination. All other numerical constants in the proofs
are either exact rational choices or checked by the supplied
programs. The extra analytic assumption is exactly the real psi
majorant in INPUT_CONTRACT.json, with exponent 27/32,
coefficient 1/64, log power 2, and x>=exp(200).

## Sources used

* **OpenAIQRH**: p.4 Theorem 1.1; zeta has no zero in Re s>7/8.
  The boundary is not excluded, and this is not full RH. The
  standard symmetry of nontrivial zeros is also stated by the
  paper (p.7, Corollary 1.2 proof). This is part of the common
  baseline, not added or revoked by D02.
* **PlattTrudgianFiniteRH**: p.2 Theorem 1, height
  3000175332800, inherited rigorous zero verification;
  p.4 Corollary 1 gives the finite-height real psi and theta
  estimates up to 2.169e25, with respective left endpoints
  59<x and 599<x. The finite psi row is retained as a possible
  E hull branch.
* **Dusart2018**: pp.3–4 §2.1 (2.1), classical explicit
  formula with midpoint jump convention under integration;
  p.5 Theorem 2.3 explicit zero density; pp.7–9
  Proposition 3.2/Table 1 and Theorem 3.3 common psi
  estimates; p.11 Theorem 4.2 theta rows; pp.12–13
  Proposition 4.3 and Corollary 4.5 for psi-theta, and
  Proposition 4.4 proof for global theta upper; pp.17–20
  Theorems 5.6, 5.7, 5.9 plus eq. (5.7), with explicit
  product/sum constants/domains in mertens.md. Proposition
  3.2 is a whole ray, not just a point-table assertion.
* **FKS**: p.3 Theorems 1.1 and 1.2 and Corollary 1.4
  (always retain the stronger pinned .8476836 and 9.22022
  coefficients for the latter); pp.4–6 Lemma 2.1,
  Remark 2.2, Corollary 2.3/Table 1; p.8
  Theorem 3.2, Remark 3.3, Proposition 3.4 identify
  different truncation formulas and an error concern; pp.21–23
  Tables 5–6. The pinned proof ranges of Theorems 1.1/1.2
  and the rows called admissible there are distinguished.
* **CH2**: p.3 Corollaries 1.2–1.3 including the centered
  unweighted formula and improved weighted von Mangoldt
  estimate for x>max(T,10^9), T>=10^7, and the all-x>=1
  substitute. For the psi centering use
  0<= (pi/T)coth(pi/T)-1 <=pi^2/(3T^2) as in p.36,
  not an unjustified exact main x. Select T<=verified height
  and check its x-domain for every use. p.34 Proposition
  9.1 (general sigma), p.35 Lemma 9.2 (signed finite psi),
  p.36 Corollary 9.3 and shape discussion, p.43 first zero,
  p.44 Lemma B.5. CH2's independent global outputs near
  exp(100) are considerably stronger than the old Dusart
  or FKS tables there, and are in the baseline.
* **PlattTrudgian2021** (1809.03134v2): pp.2–3 Theorem 1,
  Corollaries 1–2 and Table 1; p.3 Theorem 2
  (the literal real left endpoint fails as shown here);
  p.4 Lemma 4; p.7 (11) logarithmic-integral normalization
  from 2; p.8 finite Büthe comparison; pp.9–10 Lemma 6.
  Corollary 2's stated variable is log x>=2000, not
  exp(x)>=2000. Preserve the old strict tail exp(3915).
* **DudekPlatt2015** (1407.1901v1): p.2 Theorems 1.2
  (unconditional exp(9658)) and 1.3 (full-RH largest
  integer result), p.8 li sign comparison and explicitly
  identified largest integer failure up to 10^11,
  pp.9–10 computational interval analysis and Lemma 3.4.
  We do not inherit the full-RH extension.
  For the short early R join the historical integer
  computation, not their analytic RH inference, is the
  inherited premise.

## Matched-envelope procedure

For each common source bound preserve its domain and shape,
never replacing a stronger table or finite-height result by
a worse common asymptotic constant. source_tables.json records
the pinned fixed steps and shapes used in the numeric min
(Dusart Table 1, PT Table 1, FKS Tables 5–6). FKS Corollary
1.4 is included separately as applicable for x>2. Additional
parameterized recipe choices in these papers can be evaluated
over their original domains as alternatives. At the large
matched domains of our comparisons the explicit common steps
are all above the power barrier (check each at max(167,its
log onset) and use monotonicity); the explicit common
stretched-exponential shapes are above exp(-sqrt u) on their
allowed late domains, while .0017 exp(-u/8) is below that
function for u>=167 by monotonic ratio and the check at 167.
Dusart polynomial theta/psi transfers give larger bounds on
that domain as well (positive coefficients times inverse
powers; compare at 167 and differentiate their ratios).
Finite-height pi/theta branches have their finite cutoffs and
are not compared outside them. Exact common formulas like
CH2 Corollary 1.2 can be minimized over T; all such half-widths
have at least the finite height floor pi/height, which also
leaves room for the D02 improvement.

For the theoretical common comparison, compute **the same**
weighted transfer, anchor residuals, layer bounds, and
all eligible source minima with b=7/8. For D02 use b=27/32
and additionally allow the specified real psi majorant.
Rapidly decaying older and newer branches are kept at matched
domains; the ratio of the simple new power rows is proved in
mertens.md, and the stronger analytical-envelope separation
is also proved there. The independent small-range arithmetic
is applied identically in the two profiles. This is a
within-method B0 reconstruction, not an independent blind
baseline run; these are explicit supported envelopes, not
claims about every possible proof from the common sources.
