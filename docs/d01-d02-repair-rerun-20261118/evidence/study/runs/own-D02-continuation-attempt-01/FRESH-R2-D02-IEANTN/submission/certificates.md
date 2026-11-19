# Reproduction and numerical trust

Use a non-login /bin/bash, GNU C++17 as supplied, and the bound
/usr/bin/python3.10. Work in /work/submission; for example:
```sh
/usr/bin/python3.10 -B -u verify.py root gap
/usr/bin/python3.10 -B -u verify.py trade
/usr/bin/python3.10 -B mcheck.py
/usr/bin/python3.10 -B orders.py 0 6 12 19 25 50
/usr/bin/python3.10 -B tables.py > /work/tables
/usr/bin/g++ -O3 -std=c++17 -Wall -Wextra sieve.cpp -o /work/primes-cert
/work/primes-cert < /work/tables
```
Do not disable assertions (neither Python -O nor C++ -DNDEBUG).
These are ordinary executable exact certificates, not a formal model of the
compiler or source-first PV. The complete large sieve is regenerable and
has small memory; it checks 195730000000 as endpoint, not an array of that
length. The receipts in the submission are the actual program outputs.

## Interval program

Each endpoint in `verify.py` is a signed integer in units \(2^{-384}\);
rounding for multiplication is outward at both extrema of the rectangular
product, and division uses the reciprocal of a positive interval.
Exponentials reduce a point to \([-1/2,1/2]\), enclose the 48th Taylor
polynomial with remainder \(2/(2^{49}49!)<2^{-250}\), then square back.
Nonpoint arguments use monotonic endpoint reduction. Logs reduce to
\([1,2]\) via exact powers of 2, then use the odd series for
\(2\operatorname{arctanh}((y-1)/(y+1))\) through the \(199\)-th
power; the omitted sum is bounded by \(2^{-300}\) since
\((y-1)/(y+1)\le 1/3\).
Machin's identity for pi (by tangent addition with angles in the
first quadrant) and the alternating arctan series justify the pi interval.
The decimals in `*.fmt()` are display-only. All decisions are made
with directed integer endpoints. A finite test is for *entire cells*;
the coverage arguments are in the family proofs. The logged positive
residuals are in the scaled comparison units for each check.

The primepi check at the very large root uses the decreasing list
of all distinct \(\lfloor n/j\rfloor\). This list includes the small
integers below the sqrt split and is closed under further division
with floor. Initialize \(v(k)=k-1\). Before crossing out multiples
of prime \(p\), \(v(k)\) counts integers 2 through \(k\) that are
already retained primes below \(p\) or whose least prime factor is
at least \(p\). For \(k\ge  p^2\), subtract
\(v(\lfloor k/p\rfloor)-v(p-1)\), exactly the count of quotients \(\ge p\) without any smaller prime factor. Descending updates preserve
the old quotient entries. The jump \(v(p)>v(p-1)\) recognizes primes
at this stage. At \(p>\sqrt n\) no further composite survives.
No prime count data are read.

## Integer segmented certificate of finite Mertens bounds

The base sieve covers integers through 449999, more than the square
root of the final endpoint; it only crosses out using discovered primes.
Each odd segment marks precisely odd multiples of these primes
starting at or above the first multiple in range and their square.
The loops incorporate every prime once including the special case 2.
The arithmetic is integer-only (C++ with `__int128`); there is no
reliance on floating-point log, exp, or reciprocal implementations.

Use fixed scale \(W_0=2^{58}\) (called W in the C++ source, distinct
from the mathematical weighted-prime residual). For an integer \(m\),
decompose \(m=2^k y\), \(1\le  y<2\), then split by
\(y_0=(256+j)/256\le  y<y_0+1/256\), \(j=\lfloor256(y-1)\rfloor\).
Python produces lower integer approximations to \(W_0\log y_0\)
and \(W_0\log 2\), with error <2 units (checked).
The C++ routine `lg` uses \(z=\lfloor W_0(y/y_0-1)\rfloor/W_0\)
and a Horner calculation for the alternating degree 7 polynomial
for \(\log(1+z)\). Here \(0\le  z\le 1/256\); the alternating
remainder, multiplied by \(W_0\), is \(<1\). The error from replacing
the argument by \(z\) is at most one more unit. Each Horner coefficient
has rounding error <1 unit; each multiplication/division in the
recurrence costs <1 unit, geometrically damped by \(1/256\). The
final product costs <2 units including its inherited error.
Thus even with \(2k+2\) from the table and \(k\le 37\) for the prime
and endpoint integers, the claimed 128-unit error holds.
For \(\log \log m\), call `lg` with input the scaled approximate
\(\log m\) and offset 58 so the effective multiplier is \(k-58\),
small in absolute value (here \(11<\log m<27\)). The first-stage
argument error propagates by derivative \(\le 1\), so use 256 units.
Offsets keep final signed intermediates in range.

For weight \(1/p\), store \(\lfloor W_0/p\rfloor\) with one extra unit
for its upper bound. For \(\log p/p\), store integer division of
`lg(p)` by \(p\), with lower/upper allowances 1 and 2 per term
for \(p\ge 128\); the same allowances work with denominator \(p(p-1)\)
for the constants. For small primes the spare \(8192\) units
cover all extra errors: there are <128 such primes and the main log
error is divided by at least 2. For
\(c(p)=-\log(1-1/p)-1/p\), use the log difference for \(p<100\),
allowing 260 units (two log errors and one reciprocal error).
For \(p\ge 100\), the first eight series terms (degrees 2 through 9)
are obtained by integer division, with at most 2 lost units per
term from division and the recursively truncated \(p^{-k}\)
(it is in fact the exact floor before dividing by \(k\)).
The remaining series, at most \(W_0/(100^{10}(1-1/100))\)
after scaling, is less than one unit. Thus ±260 is safe throughout.

Use \(N_\gamma=2^{18}\) and
\[
 H_{N_\gamma}-\log N_\gamma-1/(2N_\gamma)
 \le \gamma \le 
 H_{N_\gamma}-\log N_\gamma-1/(2N_\gamma)+1/N_\gamma^2.
\]
To see this, sum trapezoid errors of \(1/u\) on unit cells;
the errors lie in \([0,1/(6k^3)]\) on \([k,k+1]\) by its second
derivative, giving the stated tail bound. Floor the harmonic
terms and add at most one upper unit per term, and bound the log
as above. For \(M,B_3\), accumulate prime-power corrections
through \(H_c=10^8\) and enclose the omitted constants by all
integers beyond \(H_c\). For \(M\) the tail magnitude is
\(\le 1/H_c\) (telescoping \(1/(n(n-1))\)). For \(B_3\) it is
at most \(2(\log H_c+1)/H_c<40/H_c\) by decreasing-integrand
comparison of \(2\log u/u^2\). For \(Z\), the running correction
after \(H_c\) lies between the prefix lower and global upper
bounds for the same positive subtotal.

If \(z(x)=a(x)-b(x)\), with both \(a,b\) increasing in the
nonstrict sense, every real (xin[l,r]) has
(z\(l\)-(b\(r\)-b\(l\))le z\(x\)le z\(r\)+(b\(r\)-b\(l\))).
Here each \(a\) is a prime sum (plus a constant if desired) and
\(b\) is \(L\) or \(\log L\). Use integer bounds for the two
residual endpoints, and for the log trend, and multiply by the
upper endpoint cap for \(L^2\) or \(L^3\). This is why there is no
missing coverage on prime jumps, integer gaps, or irrational
points in the 7,453,651 cells. The returned caps are rounded
upward to multiples of \(1/10000\). Each bin boundary is included
as a check point, and both sides cover it. The product conversion
is proved separately, since no product of interval approximations
is needed in the sieve. Accumulations are checked for range;
the final scaled powers use signed 128-bit (the checked pre-product
bounds are \(2^{53}, 2^{25}\) and then three powers at most; upward
shift by 16 before multiplying by 10000). All indices, shifts
and intermediate products in the log routines fit their types.

## Work and review limits

Initial external interruption is described in the supplied restoration
receipt. The initial ls command in the continuation had exit 127 (and
the shell printed its locale warning); pwd and subsequent Python reads
worked. No unavailable packet theorem was treated as executed.
All seven original text and PDF SHA256s were checked. Published
tables, RH height, QRH and the quoted finite computations retain
their original trust; no attempt to formally verify their corpus
proofs or replicate their large computational premises is claimed.

Failed improvements are informative but not falsifications of
the arithmetic conjectures: independent theta errors initially gave
a negative certificate after the Dusart sign cutoff; using the
weighted-CH2 \(J\) bound and then a directional sign switch repairs
the join. The full coefficients \(14/L, 145/L^2\), added to early
whole-ray targets, are not certified by the absolute finite-height
floor on the intermediate log range. E.g. the attempted
\(1+14/L\) ray from 55 already fails the lower-envelope cell test
near \(L=190\); \(1+14/L+145/L^2+1000/L^3\) is supported only on the
stated early window and on later rays with the appropriate last
coefficient. The order-18 tail at \(L=700\) failed; \(850\) succeeds.
For Mertens, a finite sieve ending at \(9.75\cdot10^9\) left a
visible analytic-tail constant-floor loss around \(\log x=23\).
The direct weighted averaging removes an integral inflation there,
and an extended exact sieve postpones the join to \(\log x=26\).
The individual log-power caps need not be uniformly attained;
we do not assert a smallest coefficient or largest available numerical
threshold. Reducing the final join further would require stronger
moderate-height estimates or a longer sieve (approximately \(e\)
times more range for each unit increase in the log join).

The proof of logical redundancy is exact at original trust, so it
is not possible to obtain a result requiring D01 while treating
all original premises as available, irrespective of extra searches.
There is no private reasoning transcript, no independent blind
B0 run, and no external verification stage result in this submission.
