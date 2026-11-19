# FOLLOWUP-D02 portfolio

- **ramanujan.md**: exact largest real failure (repairs the endpoint wording of the original PT theorem), normalized gap profiles through 16 nonconstant orders, finite windows, and matched B0/B1 onset and margin comparisons.
- **mertens.md**: both raw-product relative errors, the two prime sums and their exact constants, sharp real onsets for the original small-x coefficients, and whole-domain envelopes. The main late bounds replace the B0 exponent 1/8 by 5/32 and retain the 1/log x factor for reciprocal sums and products.
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

The logs are execution receipts; decimals printed by the Python interval display method are for orientation only. All sign and dominance assertions use outward intervals. source_rows.py checks both bound hashes of all seven originals and emits source_rows.json. The small sieve needs no external prime data; the much larger published Ramanujan finite computation is inherited, not rerun.

The arithmetic class uses exact 192-bit fixed-point endpoints with integer floor/ceiling. Exponentials use a Taylor bound after halving and then repeated squaring; negative tiny values are enclosed by one ulp. Logarithms use the atanh series after binary scaling; the small-sieve variant tabulates 256 rational centers and uses a shorter Taylor tail. Machin's arctangent identity and alternating rational series enclose pi. Every finite-interval certificate combines these elementary enclosures with a proved derivative, remainder or sieve invariant. Neither exploratory floating-point computations nor printed rounded endpoints are proof premises.
