# Ramanujan gap: statements, joins, and margin profiles

Use natural logarithms, x>1 real, pi right-continuous, and
R(x)=ex pi(x/e)/log x-pi(x)^2. Set L=log x. B0 and D02 are
as in spectral.md. All exponents listed as log onsets below permit
equality at the onset. All lower profile inequalities in the tables
are strict. For the overall last zero the onset is open, as discussed
below.

## The prime counting half-widths

Let V(x)=integral from 2 to x of dt/log t and A_*(v)=v e^(-v)V(e^v).
Thus the reference is Platt–Trudgian's normalization (p.7 of their
arXiv v2). The principal-value logarithmic integral differs from
this by li(2), a constant with |li(2)|<2. For instance change
variable to t=e^v in its principal-value integral, split at -1 and
bound (e^v-1)/v on [-1,log 2] by its endpoint or by 1 on the
negative part. An elementary lower bound follows as well: the
negative tail has magnitude less than e^-1, log(log 2)>-1 and the
remaining integral is positive. All uses of a finite pi bound here
allow for this additive 2.

For v>=37 put
[
 J_b(v)=E_b(v)+6S_b(v)/v+17000 v e^{-v},\quad
 T(v)=1.08e^{-v/2}+(v/3)e^{-2v/3}+v^2 e^{-3v/4}/(4\log 2).
]
Initially take B^+(v)=J_b(v)-.988 e^(-v/2) and
B^-(v)=J_b(v)+T(v), meaning
[
 -B^-(v)\ le v e^{-v}\pi(e^v)-A_*(v)\ \le B^+(v).
]
To prove this, first use J(x)=sum_(p^k<=x) 1/k. Partial summation
against psi gives the normalized error for J as
[
 g(v)+v e^{-v}\left(2/\log2+
      \int_{\log2}^{v} e^w g(w)\,dw/w^2\right).
]
For w<=20 use |g(w)|<1.5e^(-w/2) from CH2 Lemma 9.2, which
includes w down to log 2; splitting at w=2 bounds the absolute
early integral plus 2/log 2 and .1 by 17000. The .1 covers the
constant/trivial-zero part from w=20 to infinity before normalization.
On [20,v] integrate each term e^(rho w)/w^2 by parts using
1/rho. For beta>=1/8 the derivative of e^(beta w)/w^2 is at least
(beta-.1)e^(beta w)/w^2; hence the bound on the integral after
division by 1/|rho| is at most
e^(beta v)/v^2 times 1+1+.1/(beta-.1)<=6. Use (P) of spectral.md
for the square frequency sum. These finite integrals have the
justification given there. For primes powers,
[
 .988e^{-v/2} \le v e^{-v}(J(e^v)-\pi(e^v))\le T(v).
]
For k=2 the lower bound is theta(e^(v/2))/(v/2), times 1/2,
by Dusart 4.2 with eta_2=3.965; its relative loss at v/2>=18.5
is <.012. For the upper bound, theta(t)<=1.0001t and partial
summation from 2 split at e^10 give pi(y)<=1.08y/log y for
log y>=18.5: the integral after e^10 is <=1.25 y/(log y)^2 by
differentiation. The explicit numerical check appears in certify.py.
Use pi(y)<=y for k=3 and for k>=4, with at most v/log 2 terms in
the latter sum.

Take the **minimum** of these half-widths and the following
other applicable choices, independently on the two sides:
* For 24<=v<=log(10^19), both sides can use
  (1.95+3.9/v+19.5/v^2)e^(-v/2)+2v e^(-v) (Büthe bound quoted
  and used in Platt–Trudgian, original PDF p.8).
* For 24<=v<=58 both can also use
  (v^2+2v)e^(-v/2)/(8pi)+1255 v e^(-v).
  This follows from theta partial summation, their Lemma 6
  (pp.9–10) on 599<x<=e^58 and Dusart |theta(t)-t|<=t below 600.
  For the contribution from 600 onward the integrand bound is
  sqrt(t) after changing to log variable and integrating
  exp(w/2)/(8pi). At equality v=58 use the same bound.
* For 24<=v<=log(1.2*10^17), the upper side can use 2v e^(-v)
  by the sign check pi(x)<li(x) invoked in Dudek–Platt p.8 (its
  input there is not full RH).
* For v>=2000 Platt–Trudgian Corollary 2 also gives the half-width
  235 v^1.52 exp(-.8 sqrt(v)) (same V). It is not competitive with
  the new spectral tail on that domain.

## Profiles (pointwise and higher orders)

An explicit lower bound, with non-strict inequality when written
with exact V, is obtained by substituting A_*(L-1)-B^-(L-1) and
A_*(L)+B^+(L) into
[
 R(x)\ \ge {x^2\over L^2}
 \left\{ {L\over L-1}[A_*(L-1)-B^-(L-1)]
                  -[A_*(L)+B^+(L)]^2\right\}.              \tag{R1}
]
This holds for L>=25 and each side can use the tightest available
B described above; the upper bracket before squaring is >=0 because
it bounds normalized pi. The entire positive series
\[
 V(e^v)=\log(v/\log2)+\sum_{j\ge1}
       (v^j-(\log2)^j)/(j\,j!)
\]
gives certified evaluations without imported special functions.
For R1 one can also retain the lower bound zero on the connected
positivity domain, below.

Here is a polynomial profile with strict inequalities. Put
P_N(v)=sum_(j=0)^N j!/v^j. For N=20 take
r_N(v)=.5v e^(-v)+12*21!/v^21 for 24<=v<32, and
11v e^(-v)+(16/5)21!/v^21 for v>=32. For N=30 and v>=50
take 59v e^(-v)+(50/18)31!/v^31. On these domains
[
 P_N(v)< A_*(v)\le P_N(v)+r_N(v).
]
Indeed, at anchors h=24,32,50 the unnormalized differences
V(e^h)-e^h P_N(h)/h are, respectively, in (0,.5), (0,11),
and (0,59), by the series above and geometric tails. Differentiate
the unnormalized approximation: the remaining derivative is
(N+1)! e^v/v^(N+2). For v>=h>N+2, comparison with the derivative
of e^v/v^(N+2) bounds its integral from h by that function divided
by 1-(N+2)/h. This proves the remainder bounds.

Define
\[
 d^{(N)}_j=\sum_{i=0}^{\min(N,j)} i!{j\choose i}
          -\sum_{i=\max(0,j-N)}^{\min(N,j)}i!(j-i)! .
\]
These are the coefficients of z^j in
(1-z)^(-1)P_N(L-1)-P_N(L)^2 with z=1/L
(i.e. L/(L-1) in the first factor). For j>2N they are positive;
discarding that tail is lawful. The first four coefficients (0..3)
vanish; the next are d_4=1, d_5=14, d_6=145, d_7=1412,
d_8=13985, d_9=145450, d_10=1610021. The symbol d_j without
superscript denotes the full coefficient j! [sum_(i<=j) 1/i!
- sum_(i<=j) 1/binom(j,i)]. Negative coefficients beyond j>N
are **not** discarded: either evaluate them or move their absolute
values to the penalty.

Put e_+=r_N(L)+B^+(L) and
B_R=L/(L-1) B^-(L-1)+(2P_N(L)+e_+)e_+.
Then
[
 R(x)> {x^2\over L^2}\left(\sum_{j=4}^{2N}
                 d_j^{(N)}/L^j-B_R\right).                  \tag{R2}
]
The exact R1 and the strict R2 can both be retained. This is much
more than a single leading coefficient: it specifies a usable
continuous lower profile at any log argument. Also for any fixed
order N one may take a new anchor h> N+2 and enclose the residual
by the convergent V series, with two-sided remainder if the anchor
residual is negative. In particular for either cap, R admits the
full fixed-order asymptotic expansion with the d_j above: use N
larger than the order sought, the derivative remainder and the
exponentially small B^±. This is a claim at each fixed order, not
convergence of the full factorial expansion.

## Selected uniform margins and their certification

In the next two tables the profile in units x^2/L^6 is
\[
 \sum_{j=4}^{k-1}d_j/L^{j-4} + m/L^{k-4}.                 \tag{R3}
\]
Both inputs give these early closed real rays:

| k | m | log onset |
|---:|---:|---:|
|4|0|28.14|
|4|.1|28.30|
|4|.25|28.58|
|4|.5|29.12|
|4|.75|29.80|
|4|.9|30.32|
|4|1|30.74|
|5|8|32.24|
|5|10|44.92|
|5|12|45.78|
|5|14|47.04|

For m=d_k, selected higher-order rows (the exact output includes
every k=6,...,29):

| k | B0 log onset | D02 log onset |
|---:|---:|---:|
|6|216.8|185.8|
|7|249.8|210.1|
|8|283.8|235.4|
|9|318.6|261.1|
|10|353.8|287.3|
|12|425.2|340.5|
|16|569.6|448.4|
|20|715.2|557.3|
|24|861.2|666.6|
|29|1046.5|806.2|

At fixed onsets the following pairs of coefficients are supported
in (R3); B0 and D02 use exactly the same family of profiles:

| log onset | k | B0 m | D02 m |
|---:|---:|---:|---:|
|190|6|50|145|
|225|7|790|1412|
|250|8|60|13985|
|300|9|118000|145450|

Here is the entire-domain certification of the tables. The early
cells in certify.py use width 1/50 in L from 28.10 through 200,
with directed interval evaluation of R2 for **each closed slab**.
When a source estimate is out of domain anywhere in the cell,
it is not used on that cell. The cheap common half-width includes
the adaptive CH2 Corollary 1.2 and the B0 spectral coefficient
.014 e^(-v/8) for v>=190; it does not presume that the preceding
finite bound can be extended beyond its cutoff. All joins are between
valid estimates; there is no use of interpolating sample values.

For the tails let p(L) be the positive penalty in penalty_tail().
It overestimates B_R for N=30 by removing the beneficial
prime-power subtraction in B^+, replacing S by (P), using the
min of default E_h and E_cont for E_b, and absorbing negative
coefficients d_j^(30) as extra positive terms. After multiplication
by L^(k+2) this penalty is nonincreasing for
L>=max(141, (k+6)/a+1) and 4<=k<=29. For exponential terms this
follows from the scaled monotonicity in spectral.md using
v=L or L-1, with L/v nonincreasing; the polynomial factor v^2
in T and the factors 1/v are harmless on this ray. The term
L^(k+2) r_30(L) is nonincreasing (k+2<=31), and all absorbed
negative coefficients have index >31. The factor 2P_30+e_+
in the squared-error correction decreases with L. For m<=d_k
the allowed allowance after this scaling is
\[
 (d_k-m)L^2+d_{k+1}L+d_{k+2}
       +\sum_{j>=k+3} \max(0,d_j^{(30)})L^{k+2-j}.
\]
Its derivative is nonnegative on L>=140: verify
sum_(j>=2)(j-1) max(0,d_(k+1+j)^(30))/140^j < d_(k+1),
which is checked exactly up to interval divisions in the script.
Thus comparing at the indicated single tail onset proves the
entire remainder of the ray. Early k=4,5 are joined to this
argument at L=200. The resulting onsets are sufficient, not
claims of optimally solved minimax problems. At the four
fixed-onset rows, the file also verifies that using the B0
uncertainty even with an arbitrary box width in the selected
profile cannot attain the displayed D02 coefficient there.
This is failure of a B0 certificate, not a counterexample to R3.

## Connected positivity and a repair at the first real point

The early original interval is not faithfully stated by reading
the real domain of Platt–Trudgian Theorem 2 (PDF p.3) literally
at the left endpoint. Set n=38358837682. Independently,
endpoint.py proves pi(n)=1644673232 and pi(floor(n/e))=632207037,
and proves these two counts constant on [n,n+1]. It uses the
elementary distinct-floor combinatorial sieve: process p in
increasing order, detect whether p survived the smaller primes,
and remove p times a surviving integer >=p. The quotient floor
is always another key; descending key order ensures the update
uses prior-stage values. All composites have least prime <=sqrt n.
This is a finite integer proof with an interval calculation of e
and log, not a reading of plots from the papers.

On [n,n+1], R is the increasing continuous function
e x * 632207037/log x - 1644673232^2. In particular
R(n+0.1)<-7,974,585, a direct counterexample to the printed real
left endpoint. It has exactly one zero r there:
[
 38358837682.21792636509053410 < r <
 38358837682.21792636532336474 .
]
The integer branch (integers n+1 through exp(58)) of the original
Theorem 2 remains a usable inherited result. More specifically
Dudek–Platt p.8 §3.1 states the largest failing integer up to
10^11, and their computational Lemma 3.4 contains the rest of
the interval through e^28.14. Only the integer part of these
computations is needed. The needed integer stepping inequality
pi(m+k)-pi(m)<=k holds for integers m,k>=0, with strict
negativity transferred only at step lengths strictly below
the equality root. No RH error bound is used to make this join. For every real x between consecutive integers
m and m+1 with m>e, pi(x)=pi(m), while x/log x and pi(x/e) are
nondecreasing; hence R(x)>=R(m). Up to the analytic join e^28.14,
floor(x) lies in the original integer domain. The new quantitative
ray covers the join and the whole tail, so in both inputs R>0
on exactly the terminal ray (r,+infinity), with R(r)=0 and
R>=0 on [r,+infinity). The last integer failure is n under the
inherited low-range computation. Dudek–Platt Theorem 1.2 (PDF p.2)
has onset e^9658; its Theorem 1.3 has a full-RH tail and is not a
license for that tail here. The e^3915 branch in the later
Platt–Trudgian result is retained but no longer needed.

There is no incremental D02 improvement to the exact zero
threshold or to the leading early numerical margins: those
branches are already governed by finite prime counts/finite-height
pi estimates. Its effect is the stronger spectral cap, reducing
the half-widths of R1 strictly for L>=167 in the stated
portfolio (with the earlier applicable finite branches retained),
and giving the size/onset improvements certified above.
