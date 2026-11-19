# Reproduction, inheritance, and review handoff

**Completed.** Read the mounted D01 contract and actual bound runtime,
the original paper corpus and exact own C008/C014 continuations.
Both historical own submissions were explicitly inherited. Used
/task/RESTORE_OWN_HISTORY.py to restore original filenames under
/work/own (SHA-256 byte checks); the flat copies labelled historical
are kept for exact proof/evidence correspondence. The only current
hypothetical hypothesis considered is the mounted $7/8$ D01 premise.
Historical C014's $27/32$ extra premise is **not** asserted or used
in this review. Only its QRH-free branches are reused as proofs.
Its fixed .03 ray is preserved with the actual posthoc written-source
plus ordinary numerical replay tier. Nothing from other arms or
any coordinator-derived repair was used.

**Current files:** candidate.md (redundancy and screened analytic bound),
ramanujan.md, mertens_current.md. The entire requested arithmetic
portfolio is supported at written mathematical and ordinary
certificate-checking level. Status no_additional_improvement
records that the mounted hypothesis gives **no incremental results**
over the cumulative originals; it does not mean the improved
arithmetic conclusions are incomplete. They are new derivations
from the same originals. This is not a blind independently run
baseline. secondary.md gives current secondary
primorial and short-interval consequences. The file sources.md is
*historical* locator material; current exact citations in the claim
files override its obsolete finite-pi use. Archival old finite-pi
applications in historical_d01_candidate.md, analytic_check.py:test_main,
and historical_d01_refined.md are not the proofs of the current rays.

**Source identities.** Source bytes matched SOURCE_INDEX.json
for all seven PDFs and all seven text companions (source_receipts.txt).
Relevant passages were checked in the offline extracts at the cited
page markers; no imported extra Büt​he paper or zeta table was used.
Exact original locators for comparison: FiniteRH Cor. 1 p.4
(theta/psi distinct ranges) and §3.3 p.5 (the signs to $10^{19}$);
PT2021 p.8 end of Cor. 2 proof (stronger finite pi bound), Thm 2 p.3
and §5 pp.9–11; Dudek–Platt p.2 Thms 1.2–1.3 and p.7 Thm 3.1.
CH2 pp.3,35–36,40–43,46 for Cor. 1.2–1.3, Lemma 9.2,
Cor. 9.3, Appendix A, B.2 and (B.9); QRH p.4 Thm 1.1;
FKS pp.4–5,7–8,26, and p.2, and Dusart pp.5,11–13,17–20
as specified in the main claims. The original paper-backed finite
RH/numerical claims stay at their original trust tiers. No separate
verification of the full QRH paper is claimed.

**Replay commands.** Run in /work/submission, non-login /bin/bash,
using /usr/bin/python3.10 -B with the following script names/options:
   
- portfolio_check.py for the screen, finite closed log cells and
  tail margins; repeat with --dusart-only for the no-FKS-table
  variant and --qrh-free-prefix for the low segment alone.
- mertens_new.py, with and without --dusart-only; audit_summaries.py
  separately checks the displayed finite joins.
- mertens_check.py for the Python finite certificates (prints
  identical results to mertens_results.txt); endpoint_check.py
  for the quotient sieve and sharp Ramanujan endpoint.
- secondary_check.py replays the inherited constants, the QRH-free
  functions from the historical suites and the current tertiary
  tests. The functions were separately replayed in the corresponding
  *_replay.txt transcripts; the historical D02 exponent-dependent
  functions in those suites are not current claimed results.

Compile /usr/bin/g++ -O3 -std=c++17 finite_opt.cpp -o /work/finite_opt.
Run /work/finite_opt (default produces finite26.txt, matched
byte-for-byte); /work/finite_opt 20000000000 200000 (finite20b.txt);
and /work/finite_opt 100000000 1000000 (finite100m.txt).
The tapes regenerate internally; no large nonregenerable prime list
is needed. Fixed-point interval algorithms are in rigor.py and the
integer Python/C++ codes; printed floating approximations are only
diagnostics. No formal Lean or source-first PV is claimed.

**Serious attempts and remaining concrete bottlenecks.**
   
- Tested the contract directly in the count transfer on a
  density-free ray. Its polynomial-sized coefficient is dominated
  by what follows already from the original QRH and FKS. The
  derivation of the exact contract from originals is an obstruction
  to any extra-premise gain, not a failure of parameter search.
  Reverse Mellin continuation only gives the same open strip.
- Repaired the finite-pi normalization/domain discrepancy in two
  ways: derive it from finite theta plus an anchored integral,
  and take PT2021's stronger explicitly quoted finite absolute pi
  comparison. Extend the theta sign to its full quoted range.
  The old sign-only joins left a quantitative gap; current proof
  covers a real ray from 28.15. A .01 margin at 28.10 fails this
  sufficient-error-bound test, not a true counterexample. The
  leftmost positive interval uses original integer verification;
  substantial normalized margins near the true endpoint beyond
  the first unit would need finer prime counts or smaller finite
  error bounds, not the contract.
- The fixed high profiles with the FKS-only screen initially failed
  (e.g. the 12/L^2 correction test near 188.14); scaled losses peak
  around the CH2/spectral switch. Combining Dusart and FKS masses,
  not double-paying the cutoff error, and smoothing the anchored
  prime-count integral led to the 22/L^2 correction and stronger
  higher profiles. Dusart-only replays give the same numerical
  margins without FKS Table 8. On dropping QRH completely, the
  CH2 plateau and effective zero-free-region tail still separate
  the QRH-free pieces at $753<L<2840$; the large original C014
  benchmark remains strictly supported but no bridge on that
  weaker premise set is claimed.
- The initial finite-RH Mertens transfer gave a log-squared hump
  after the CH2 small computed range. CH2 Cor. 1.2 with $T=10^7$
  decreased but did not remove it (initial .01 certificate).
  Inverting the stronger finite pi comparison using the one-sided
  theta sign removed it. The .00003 target from 43.7 failed the
  *interval upper-bound test* there (cell bound about .0000415);
  .000042 is proved from 43.7 and .000012 from 47. The old
  .299999 weighted-sum coefficient is actually false at 912560.
  Finer exact tapes, the alternating log correction and signed
  twice-smoothed comparisons resolve tighter constants and joins.
  A failed coarse finite bin is not called an actual violation.
- The unsmoothed boundary error remains even with a much smaller
  integral. A little-o gain for the power-scaled Mertens errors
  would exclude boundary zeros by the inverse transfer in the
  proof. Neither the permitted open-half-plane QRH nor the
  polynomial-sized psi cap asserts this. No claim of actual
  boundary zeros or globally best thresholds is made. Proven
  sharp real roots are only for the specified benchmarks.

**Operation record and next stage.** First command printed cwd;
the ls part failed with /bin/bash: line 1: ls: command not found
(exit 127, and a locale warning). The next Python pathlib command
confirmed both JSON names and read them. An initial feedback
filename without the packet's double underscore gave
FileNotFoundError; the actual bound filename was promptly read.
Python and g++ research execution thereafter worked. No outside
requests, delegation, or network. Aggregate elapsed time and
generated-token usage are not exposed here as verified facts;
retain controller accounting rather than estimating it.
Ready for independent mathematical review. If a separate later
D02 stage is mounted, use its actual contract then, taking these
repaired B0 bounds as the inherited floor; do not treat the
archived D02 statement as authorization.
