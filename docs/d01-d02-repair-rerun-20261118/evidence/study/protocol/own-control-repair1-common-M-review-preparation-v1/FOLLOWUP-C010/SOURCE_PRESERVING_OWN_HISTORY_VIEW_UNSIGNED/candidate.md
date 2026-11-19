# FOLLOWUP-D02 — repaired research portfolio

Both families are ready for independent **re-review**. B0 uses
the supplied originals at stated trust; B1 adds exactly the
hypothetical direct-\(\psi\) majorant in INPUT_CONTRACT.json.
Full RH is not assumed. The B0 comparator is a matched
reconstruction, not a blind baseline run or an optimality claim.

* **Ramanujan.** The exact last real failure remains the equality
  point in \((38358837682.217926,38358837682.217927)\), at inherited
  finite integer-computation trust. The strict real sign ray
  starts just after it; the new input improves quantitative
  profiles, not this already sharp sign onset. For instance with
  \(L=\log x\), the lower bound
  \(R>(x^2/L^6)(1+14/L+80.9/L^2)\) is certified from \(L=48.95\)
  under B1, versus \(L=196.58\) in the matched B0 certificate.
  The full coefficients through order 12 are tabulated, with
  matched B0/B1 onsets 575/450 for order 12. Without using
  FKS's density corollary, the full order-2 coefficient is
  attained at log-onsets 316/239. See ramanujan.md and advance.md.
* **Mertens.** At \(L\ge200\), .254039 times \(x^{-5/32}/L\)
  bounds both relative product errors and the reciprocal-prime
  sum error; .254039 times \(x^{-5/32}\) bounds the weighted
  prime-sum error. The matched refined B0 constant .018115
  uses exponent \(1/8\), and B1 wins on the entire matched
  ray. The repaired full envelope and the combined Ramanujan
  profile improve strictly in the listed comparison from
  \(L=168.745\); independent of the density corollary both strict
  comparisons are available from 342. Without density, at
  \(L\ge300\) the B1 constant .00408 bounds the same channels
  with factors \(Lx^{-5/32}\) and \(L^2x^{-5/32}\), improving
  the previous .0626 there. The earlier least-real-onset
  results and improved finite signs are B0 secondary results.
  See mertens.md, repair.md and advance.md.
* **Method and repairs.** The hypothesis gives an all-height
  zero cutoff through Mellin continuation, not an artificial
  replacement of the original QRH conclusions. A two-pole
  Perron kernel gives an absolutely convergent primitive;
  a further positive Laplace-weight transfer retains smaller
  product and sum errors. repair.md addresses each prior defect,
  including the FKS small-domain problem, the \(C(L)\) slope,
  PT §5's early auxiliary and published-anchor bounds, and the
  conversion conditions. The FKS coefficient-2 curve now enters
  only on its proved segment with least onset in
  \((2.29012,2.29014)\). No source's false real inequality or
  unsupported small-input estimate is used as a premise.

## Replay

From this directory with the offline interpreter:
    
    /usr/bin/python3.10 -B bounds.py all
    /usr/bin/python3.10 -B finite_m.py
    /usr/bin/python3.10 -B repair.py
    /usr/bin/python3.10 -B advance.py certify

The first two outputs match the old replay.txt and finite_replay.txt;
their fresh transcripts are repair_original_replay.txt and
repair_finite_replay.txt. New evidence is in repair_replay.txt and
advance_replay.txt. The optional advance.py explore mode is **not**
a whole-ray proof. Directed Decimal arithmetic uses 48 significant
digits; arithmetic operations are outward and exp/ln enclose their
correctly rounded implementations by adjacent Decimal numbers.
Pi uses Machin's identity; finite counts and sieve use exact integer
operations. The written proofs supply the domain and monotonicity
arguments for numerical tests. No Lean or source-first PV is claimed.

sources.txt records the SHA-256 receipts for all seven originals and
extractions. prior_* files preserve original changed payload bytes.
attempts.md and work_accounting.json record research and remaining
bottlenecks; LOCK.json binds all payloads.
