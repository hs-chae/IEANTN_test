# FOLLOWUP-D02 portfolio — planned own-review repair

- **upgrade.md**: strongest current statements and repair-stage proofs. The B0 Ramanujan F0 ray now starts at log x = 30.75; B1 advances the matched late profiles through order 43, including density-free branches. For Mertens, there are improved constants and real onsets and a stronger density-free B1 envelope.
- **ramanujan.md**: exact largest real failure (repairs the endpoint wording of the original PT theorem), normalized gap profiles through 16 nonconstant orders in the retained base portfolio, finite windows, and matched B0/B1 onset and margin comparisons.
- **mertens.md**: both raw-product relative errors, the two prime sums and their exact constants, sharp real onsets for the original small-x coefficients, and whole-domain envelopes. The main late bounds replace the B0 exponent 1/8 by 5/32 and retain the 1/log x factor for reciprocal sums and products.
- **REPAIR.md**: exact reviewed defects, changes, corpus/source ledger, reproduction and limitations.
- **common.md**: analytic transfer of the extra input to a zero-free half-plane, zero-density compression, signed contour argument, and source/trust ledger.

## Replay

With the bound original packet mounted as in RUNTIME_PATHS.json, run from this directory:

    export PYTHONDONTWRITEBYTECODE=1
    /usr/bin/python3.10 certificate.py
    /usr/bin/python3.10 refine.py
    /usr/bin/python3.10 endpoint.py
    /usr/bin/python3.10 small.py
    /usr/bin/python3.10 source_rows.py
    /usr/bin/python3.10 checks.py
    /usr/bin/python3.10 upgrade.py

Alternatively run /usr/bin/python3.10 replay_portfolio.py (reruns the seven current scripts and refreshes the logs and replay_repair.json; regenerate LOCK.json after replay if using it as a new payload). The prior_* files preserve original exact bytes and are historical, not current claims. The logs are execution receipts; decimals printed by the Python interval display method are for orientation only. All sign and dominance assertions use outward intervals. source_rows.py checks both bound hashes of all seven originals and emits source_rows.json. The small sieve needs no external prime data; the much larger published Ramanujan finite computation is inherited, not rerun.

The arithmetic class uses exact 192-bit fixed-point endpoints with integer floor/ceiling. Exponentials use a Taylor bound after halving and then repeated squaring; negative tiny values are enclosed by one ulp. Logarithms use the atanh series after binary scaling; the small-sieve variant tabulates 256 rational centers and uses a shorter Taylor tail. Machin's arctangent identity and alternating rational series enclose pi. Every finite-interval certificate combines these elementary enclosures with a proved derivative, remainder or sieve invariant. Neither exploratory floating-point computations nor printed rounded endpoints are proof premises.
