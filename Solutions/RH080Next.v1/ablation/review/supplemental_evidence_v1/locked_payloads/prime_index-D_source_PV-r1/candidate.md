# Growing-rank transport for the supplied prime-population curves

Write (p_n=operatorname{nth}(mathrm{Prime},n)) with (p_0=2),
(L(x)=sqrt{x}log x), and (J_n(b)=lfloor bsqrt{p_n}
floor+1)
for (bge0). Define the exact affine profiles
[
G(b)=rac{20582561296}{24680948495}(1+2b),qquad
S(b)=rac{944247+1163388b}{10^6},qquad
F(b)=rac98+rac{16}{15}b,
quad B(b)=min(S(b),F(b)),quad D(b)=min(G(b),B(b)).
]

**Fixed-cutoff theorem.** Fix (etage0). Under ordinary zeta RH and
(	exttt{CMSFunctionalInput.v1.population_reduction}), for each fixed
(arepsilon>0) there is an (n_0) such that simultaneously for all
(nge n_0, 1le jle J_n(eta)),
[
0<p_{n+j}-p_n<(G(eta)+arepsilon)L(p_n).
]
Under ordinary zeta RH and both
(	exttt{BRFourierInput.v1.norm_identity}) and
(	exttt{BRFourierInput.v1.uniform_population_q1}), the same statement
holds with the exact width (B(eta)), without epsilon. With all these
inputs take (min(G(eta)+arepsilon,B(eta))).
For *each of these fixed widths* (c), there is even a fixed (eta>0)
such that eventually the strict upper bound is (cL(p_n)-etasqrt{p_n})
for the larger range (1le jle J_n(eta+eta)).

**Rank-adaptive theorem.** With all the inputs and for each fixed
(arepsilon>0), eventually, simultaneously for the same (j) as in
the fixed-cutoff theorem, put (t=(j-1)/sqrt{p_n}). Then
[
0<p_{n+j}-p_n<min{D(t)+arepsilon, B(eta)} L(p_n).
]
With only the CMS package replace the minimum by (G(t)+arepsilon).
With only the BR package it is (min{ B(t)+arepsilon, B(eta)}).
These are simultaneous estimates, not a pointwise theorem with a threshold
depending on (j) or (t). The epsilon-free statement for the leading
profile is a uniform limsup:
[
limsup_{n	oinfty} max_{1le jle J_n(eta)}
left(rac{p_{n+j}-p_n}{L(p_n)}-D((j-1)/sqrt{p_n})
ight)le0.
]
In particular the limsup of the maximal normalized gap is at most (D(eta)).
The Gaussian width is not asserted with (arepsilon=0) as an eventual
bound. Where (B(eta)le G(eta)) the exact width (D(eta)=B(eta))
is attained as an eventual strict upper bound using the BR package instead.

## Exact bridge and simultaneous margin

The infinite set of primes has a strictly increasing enumeration; its
range is the primes and (p_nge n+2) by strict increase from (2).
Let (yge p_n). For a nonnegative real (y) the nonnegative natural floor
counts primes (le y), and the natural ceiling gives
(pi^{<}(y)=mathrm{Nat.primeCounting'}(lceil y
ceil)), the count of
primes (<y): for an integer (mge0), (m<y) iff (m<lceil y
ceil).
In a count of an initial segment of the primes, index (k) is included
iff the count exceeds (k). In particular (pi_{mathbb R}(p_n)=n+1).
Thus for (jge1),
[
egin{aligned}
p_{n+j}le y &iff jle pi_{mathbb R}(y)-pi_{mathbb R}(p_n),\
p_{n+j}< y &iff jle pi^{<}(y)-pi_{mathbb R}(p_n).
end{aligned}
]
The order equivalences hold also with truncated natural differences when
(0le y<p_n), since both sides are then false. The exact second count
for (yge p_n) equals the first count minus the indicator that (y)
is an integer prime. Indeed the only possible extra member of the first
set is (y) itself. In particular (Nge j) gives only a weak endpoint
unless that indicator vanishes; (Nge j+1) suffices for strictness. For
instance (j=1,n=0,y=3) has (N=1) but (p_1=y).

Given (mathrm{GoodCoefficient}(eta,c)), let (delta>0) be its
margin and evaluate at (x=p_n); eventually the real-variable threshold
holds by (p_nge n+2). Put (eta=delta/4) and assume also
(deltasqrt{x}>8). For each (jle J_n(eta+eta)),
[
N(c,x)-j ge (delta-eta)sqrt{x}-1 > etasqrt{x}+2.
]
In particular the order bridge gives (z=p_{n+j}le y=x+cL(x)).
The residual count (N(c,x)-j=pi_{mathbb R}(y)-pi_{mathbb R}(z))
counts only distinct integers in ((z,y]); it is bounded by
(lfloor y
floor-zle y-z). This gives the stated shorter width,
with strictness; positivity follows from strict increase. Without the
shorter width, the single unit lost at the endpoint is already covered
by the margin. No explicit onset is extracted.

For the rank-adaptive version, (0le tleeta), and (tle b)
implies (j-1lelfloor bsqrt{p_n}
floor). For an affine profile
(A(t)=a+s t), (sge0), choose (d=arepsilon/(2(s+1))) and apply
the fixed-cutoff theorem at the finite grid (kd) for
(0le klelceileta/d
ceil), with tolerance (arepsilon/2).
For BR this tolerance is gratuitous: the exact bound already implies it.
Intersect those finitely many eventual statements. Given (j), use
(k=lceil t/d
ceil); then (tle kdle t+d) and
(A(kd)+arepsilon/2le A(t)+arepsilon).
Run this for (G,S,F) and intersect with the fixed-cutoff BR statement.
Taking the maximum and then the limsup for each fixed epsilon proves the
uniform limsup inequality. No interchange of an uncountable intersection
and eventuality is used.

## Exact lower-envelope comparisons, scope of “strongest”

The slopes satisfy (0<16/15<1163388/10^6<2q) for
(q=20582561296/24680948495), and the intercepts satisfy
(q<944247/10^6<9/8). The (G,S) intersection is
(u=544470055511653/2490320656859788); the (S,F) intersection is
(v=542259/290164). Since (0<u<v), at (u), (G=S<F), and at
(v), (F=S<G). Slope ordering gives (D=G) up to (u), (D=S)
between (u) and (v), and (D=F) above (v), with ties as specified.
For a fixed positive epsilon use the literal minimum, not these
epsilon-free switch points. At (eta=0) the cutoff is exactly one.
At (eta=1) the best of the three printed lines is
(S(1)=421527/200000=2.107635), strictly below the preserved explicit
baseline (343827/160000=2.14891875), but only eventually.

This is the lower envelope of the three stipulated curves, not an
optimality claim for widths deducible from RH or all the information in
the witnesses. Under its separate named RH+Green+Nicolas+BPT package,
the preserved baseline has its own strict-open inequality and explicit
onset. Its limiting line ((9/8)(b+18203/20000)) is in its original
width domain exactly for (973/180000le ble2396173/180000).
On that domain (B) is strictly below the leading line (compare
(S) for (ble2), (F) for (bge2)).
This is only a leading-coefficient comparison, not a finite-x comparison
to the baseline's positive (4.2/log x) term. No (exp(24)) onset,
upper width restriction, or baseline hypotheses transfer to the new theorems.

## Optional n-only normalization (written; extra prime-growth input)

Add the prime number theorem in the form
(pi_{mathbb R}(x)sim x/log x) as (x	oinfty); this is not a
premise of the main result. CMS v2 immediately after (1.12) explicitly
states this asymptotic. At (x=p_n), the exact identity yields
(p_n/log p_nsim n). Taking logs gives
(log n=log p_n-loglog p_n+o(1)); as
(loglog p_n/log p_n	o0), this implies
(log p_nsimlog n) and (p_nsim nlog n).
Hence (sqrt{p_n}sim R_n:=sqrt{nlog n}) and
(L(p_n)sim T_n:=sqrt n(log n)^{3/2}).
Fix (etage0). For any (c) in the fixed-cutoff theorem,
the larger rank margin (eta+eta) ensures that
(lflooreta R_n
floor+1le J_n(eta+eta)) eventually.
Thus for each (
ho>0) the same gaps are (<(c+
ho)T_n) on this
n-only cutoff. In particular under all inputs one gets
((D(eta)+
ho)T_n) for each (
ho>0) by splitting the slack
between the original width and the change of scale.
In the opposite direction, asymptotic equivalence alone does not
guarantee the exact floor inequality at the same (eta) without
using the rank margin or increasing (eta). No explicit PNT
error estimate is invoked, and no prime-growth result is assumed
without this named premise.

## Verification

Run `/bin/lean /work/submission/Transport.lean` using the assigned
wrapper and object mounts. The exact order equivalences are
`le_endpoint_iff`, `lt_endpoint_iff`; the endpoint correction is
`endpoint_indicator`; the stronger fixed-width bridge is
`transport_with_margin`. Named applications are `gaussian`, `br`,
`br_source`, `combined_source`. The finite-grid proof is
`affine_profile` and the combined consumer is `combined_profile_source`.
All are in namespace `RankTransport`. Lean checks the transport on top
of frozen theorem objects. The three analytic input propositions and
ordinary RH are explicit parameters, not proved by computation or added
as Lean axioms. See the separate audit for the provenance boundaries.


## Separate witness-level refinement (not from the rounded curves alone)

The same supplied BR certificates yield strict transport for every fixed
(c>min(S_*(eta),F_*(eta))), where the exact rational affine functions are
[
S_*(b)=rac{88772107263302791}{94013706369423310}
   +rac{10937434262266196}{9401370636942331}b,qquad
F_*(b)=rac{8963801668855556368}{7999999999999999995}+rac{16}{15}b .
]
No new analytic premise is needed. For each witness with attained peak
(M>0), denominator (H>0), and certified mass upper bound (U), BR's
lower principal term is at least ((cH-U)/(2M)). The respective raw
line is ((U+2Mb)/H). Strict separation of (c) from that line supplies
a positive margin after the vanishing remainder. Apply the same bridge.
Both raw lines are strictly below their respective printed lines for
(bge0); the midpoint of their minimum and (B(b)) gives an exact
choice strictly below (B(b)). Equality at the raw minimum is not
claimed. With all analytic inputs one can take the minimum of this
refined BR width and (G(eta)+arepsilon).
Lean: `br_refined_source`, `sparseRaw_lt_line`, `flatRaw_lt_line`.
