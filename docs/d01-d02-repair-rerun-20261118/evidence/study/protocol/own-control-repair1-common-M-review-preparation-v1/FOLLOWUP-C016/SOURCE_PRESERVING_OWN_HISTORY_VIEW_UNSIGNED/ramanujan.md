# Ramanujan gap: connected domain, normalized margins, and high-order profiles

Read spectral.md for exact premises and the all-real estimates $S_{7/8}$ (B0) and $S_{27/32}$ (B1). Put $L=\log  x$ and $r(x)=L^6 R(x)/x^2$, where $R(x)=e x\pi(x/e)/L-\pi(x)^2$.

## 1. Connected sign domain, including the real endpoint correction (B0)

Let $n=38358837682$. Define $r_*$ as the unique root in $(n,n+1)$ of
$$
 \frac{et}{\log t}\cdot 632207037=1644673232^2.
$$
Then **$R(x)>0$ for every real $x>r_*$**, and $R(r_*)=0$. At integer arguments the least inclusive permanent onset is $n+1$. The root lies strictly between $n+0.217926365$ and $n+0.217926366$. In particular a sufficient inclusive real onset is $n+0.217926366$. The strict ray cannot extend left of $r_*$, and replacing that open endpoint by a closed one would be false.

Here are the proof and trust details. pcount.cpp and endpoint.py independently count
$\pi(n)=\pi(n+1)=1644673232$ and $\pi(14111427770)=632207037$. The certified interval for $x/e$ throughout $[n,n+1]$ lies strictly between 14111427770 and 14111427771, so both counts are constant there. $et/\log  t$ is strictly increasing there. The checked endpoint signs and exact root give the assertion in that unit interval, including the counterexample at $n+0.001$ by monotonicity. The literal all-real left endpoint of Platt--Trudgian PNT (arXiv:1809.03134v2), PDF p.3 Thm.2, should not be imported: it conflicts with these reproducible counts. We use the inherited integer finite computation above $n$ to $10^{11}$ (Dudek--Platt arXiv:1407.1901v1 PDF p.8, 'Computation'; not their RH-dependent infinite tail). In each $[m,m+1)$ for $m\ge n+1$, the first count $\pi(x)$ is constant and $\pi(x/e)$ is nondecreasing, so $R(x)\ge  R(m)>0$. The remaining finite segment through $1.15\cdot10^{16}$ is Dudek--Platt Lemma 3.4 (PDF p.10). That finite evidence is inherited, not a new replay of the enormous verification. The independently derived analytic tail starts already at $L=36.9$, with $e^{36.9}<1.15\cdot10^{16}$. Thus the misworded PNT Thm.2 is not needed for **any** part of our connected-domain proof. Neither the B0 nor the B1 sign theorem uses full RH. The published disjoint sign domains and the original tails at $e^{3915}$, $e^{9658}$ need not be used beyond the finite segment.

The integer counter program stores the descending distinct quotients $v=\lfloor  N/i\rfloor $, initially with count (v-1). When processing a prime $p$, the data count numbers (ge2) with no prime factor below $p$, together with the already processed primes. $p$ survives precisely when the counts at (p,p-1) differ; if $v\ge  p^2$, remove precisely the (pm) with (mge p) surviving that test, numbering $S(\lfloor  v/p\rfloor )-S(p-1)$. The child quotient occurs in the same list and is smaller, hence not yet updated on that pass. All $1\le  v\le \lfloor \sqrt  N\rfloor $ occur as a contiguous suffix; for larger $v$ the zero-based index is $\lfloor  N/v\rfloor -1$. After processing through $\lfloor \sqrt  N\rfloor $ the survivors at $N$ are exactly the primes. All integers fit in the specified machine widths. endpoint.py also checks end signs by outward decimal intervals with the proof contract in notes.md.

## 2. Certified whole-ray menu

Every line asserts $r(x)>$ the displayed entry for **all real** $L$ at least the given cutoff. Decimals are exact decimal rationals. Let
$$
 g_n=\sum _{j=0}^n\bigl (n!/j!-j!(n-j)!\bigr ),\qquad 
 H_N(L)=\sum _{n=4}^{N}g_n/L^{n-4}.
$$
The first entries $g_4,\ldots ,g_{11}$ are $1,14,145,1412,13985,145450,1610021,19063832$.

| Normalized margin | B0 sufficient $L$ | B1 sufficient $L$ |
|---|---:|---:|
| 0 (analytic branch alone) | 36.9 | 36.9 |
| $0.5$ | 40.5 | 40.5 |
| $0.9$ | 42.3 | 42.3 |
| (1) | 42.9 | 42.9 |
| $1+14/L$ | 47.4 | 47.4 |
| $1+14/L+5/L^2$ | 48 | 48 |
| $1+14/L+7/L^2$ (matched onset) | 49.1 | 49.1 |
| $1+14/L+78/L^2$ | implied by the B0 100-row at 200.1 | 49.1 |
| $1+14/L+100/L^2$ | 200.1 | 172 |
| $H_6$ | 221 | 187 |
| $H_7$ | 254 | 211.5 |
| $H_8$ | 288.5 | 237 |
| $H_9$ | 323.5 | 263 |
| $H_{10}$ | 359 | 289.5 |
| $H_{11}$ | 394.5 | 316 |
| $H_{26}$ | 939.5 | 724 |

For orders $12\le N\le25$, use the intermediate whole-ray cutoffs in high_receipt.txt too.

Also $r(x)>0$ on (37.2le Lle39.47), and $r(x)>0.5$ on (38.5le Lle39.47), both on B0. These finite quantitative branches are kept even though they do not give those constant margins on the next interval. See cert.py and the receipt for the exact checks. All cutoffs are inclusive in $L$; actual $x$-cutoffs are their exponentials, not integer roundings. The large polynomial menu is subordinate to the stronger pointwise bound below, rather than a claim of best possible coefficients or cutoffs.

## 3. A squared-source ODE for the smooth gap

This avoids subtracting independent asymptotic remainders at order $L^{-6}$. Let $\ell=\log  600$. Define
$$
 F(v)=\pi(600)+(600-\theta (600))/\ell+\int _{\ell}^{v}e^t/t\,dt,\qquad  A(v)=v e^{-v}F(v).
$$
This is a chosen anchored comparison function, not an unidentified variant of (operatorname{li}). Partial summation gives the exact identity
$$
 v e^{-v}\pi(e^v)= A(v)+ E_\theta (v)
       + v \int _\ell^v e^{t-v} E_\theta (t)/t^2\,dt,\qquad 
 E_\theta (v)=e^{-v}\theta (e^v)-1 .
 \tag {R1}
$$
Let $B(L)=Le^{1-L}F(L-1)$, $C=B-A^2$, and $\kappa =1-1/L$. Differentiation gives $A'+\kappa  A=1, B'+\kappa  B=1/\kappa $, hence exactly
$$
 C'+\kappa  C=\kappa  (A-1/\kappa )^2 . \tag {R2}
$$
On (Lge34) we have $P_{27}(L)\le  A(L)\le  1+1/L+3/L^2=U_A(L)$, with $P_N=\sum _{j=0}^N j!L^{-j}$. Indeed $P_N'+\kappa  P_N=1-(N+1)!L^{-N-1}$, while $U_A'+\kappa  U_A=1+L^{-2}-9L^{-3}\ge 1$. Check both barriers at 34 and propagate by the integrating factor. Also $L^4 C(L)>H_{27}(L)$ there. For the latter comparison, set $z=1/L$. The lower barrier for $A-1/\kappa $ is
$$
 D(z)=\sum _{n=2}^{26}(n!-1)z^n+(27!-2)z^{27},
$$
using $z/(1-z)\le 1$ in the omitted geometric tail. It is positive. In the differential comparison, subtract $(d/dL+\kappa )\sum _{n=4}^{27}g_nz^n$ from $(1-z)D(z)^2$. Coefficients through degree 27 cancel; the coefficient at 28 plus the absolute worst unfavorable contribution at $z\le 1/34$ is positive. cert.py verifies these integer/rational polynomial facts and $C(34)>\sum _{n=4}^{27}g_n/34^n$. In computing $F(34)$, $F(33)$, it enumerates primes at the anchor and uses the series antiderivative $\log  t+\sum _{j\ge 1} t^j/(j,j!)$ with truncation at 190 and a geometric tail. Thus both differential inequalities are strict where needed and require no asymptotic sign heuristic. Higher profile terms are not computed by unstable floating subtraction of the two large main terms. A still stronger main curve for the pointwise envelope is $L^4 C(L)$ itself, with its exact definition or its ODE for computation.

## 4. Error transport, joins, and exact pointwise comparison

Let (d$v$) be an upper bound on $v^4$ times the absolute error in (R1). For (ellle vle58) use
$$
 d_f(v)=\frac {v^6+2v^5}{25}e^{-v/2}.
$$
This integrates the finite-RH $\theta $ error exactly up to enlarging the constant $(8\pi>25)$. On (vge58) choose a positive exponential-polynomial $\psi $ envelope (J$v$) from (J_{
m CH}, S_{7/8}), and, under B1, $S_{27/32}$. Add the two Dusart prime-power terms $1.000000147e^{-v/2}$, $1.78e^{-2v/3}$. For each resulting term $c v^k e^{-a v}$, use in (d$v$)
$$
 c v^{4+k}e^{-a v}\left (1+\frac {1}{v(1-a-2/58)}\right )
$$
and add once $ (2/25)v^5 e^{29-v}$ for the earlier interval. This bound follows by integrating $e^{(1-a)t}t^{k-2}$, whose logarithmic derivative is at least $1-a-2/58>0$. Take the minimum of the legal transported envelopes. When (Lle39.47), the upper error in (A$L$) can instead be set to zero: Dusart PDF p.13 proof of Cor.4.5 supplies $\theta (t)<t$ for $t<1.39\cdot 10^{17}$, containing the whole integration range $[600,e^L]$. For the lower error always use the absolute envelope.

Writing $d_+$ for the upper error (zero on this signed branch), we conclude
$$
 r(x) \ge  L^4 C(L)
    - \left (\frac {L}{L-1}\right )^5 d(L-1)
    - 2U_A(L)d_+(L)-\frac {d_+(L)^2}{L^4}. \tag {R3}
$$
Use this for (Lge34). This is already a whole-domain curve (possibly negative on some parts), not an asymptotic placeholder. One may strengthen it by replacing $U_A$ by the exact $A$; using signed $\theta $ intervals and integrating pointwise minima in (R1); or using a direct original $\pi$ bound converted to an interval on $\pi(e^v)$, then intersecting intervals. Such an intersection carries along, e.g., PNT paper Cor.2 on its original (Lge2000) domain with its $\int _2^x dt/\log  t$ normalization. For a lower bound, use the lower $\pi(x/e)$ and upper nonnegative $\pi(x)$. Retain the maximum of these valid lower profiles, the polynomial rows on their domains, and the sign bound on its connected domain (with the strict vs non-strict conventions as above).

Additionally $A$ of spectral.md can be transported without absolute integration of its high-zero sum. For (vge62), the contribution to the absolute normalized error in (R1) from the high spectral endpoint and its integral over $[62,v]$ is at most
$$
 Z_b(v)\left[1+\frac {1}{Hv}\left (1+\frac {2}{v(3/4-3/62)}\right )\right ]
 + \frac {v e^{62-v}Z_b(62)}{H62^2}.
$$
Integrate $e^{\rho  t}/t^2$ once by parts; bound the last integral using the logarithmic derivative $\beta -3/t\ge 3/4-3/62$. Transport $D_b$ and the Dusart powers from 62 by the preceding positive-envelope rule with 58 replaced by 62, and bound the earlier integral by the indicated finite-RH and CH $\theta $ envelopes. This gives another valid branch for the maximum, not needed for the numerical menu.

Whole-ray verification in cert.py: on each finite rational block bound every positive main monomial using the right endpoints, and each negative monomial using the left endpoints. For errors beyond 58 all multiplied exponential terms except the CH constant-rate term decrease; the latter increases and is evaluated at the right endpoint. On the first finite-RH branch $d_f$ decreases for (vge33). The factor $L/(L-1)$, $U_A$ and $1/L^4$ decrease. Split at each finite join for both (L,L-1), taking the larger interval budget if a block crosses a join. Choose the best **block** budget before subtracting. With $j$ the index of the first positive residual coefficient in $H_{27}-\text {tar\ge t}$, test the final cutoff for $L^j$ times the entire loss versus that coefficient; all scaled spectral terms $including the squared term and shifted error with (L/(L-1)) fac\to rs$ are nonincreasing once $L-1\ge (6+j)/(1/8)$. No extrapolation of a grid into the tail is used. The $H_{26}$ rows only require this tail test using the $g_{27}$ surplus.

For the *sharper early joins*, CH2 PDF p.36 Cor.9.3 (9.4) with $T=2\pi^2 e^{v/2}/v$ gives a $\psi$ error coefficient
$$
 c(v)=((v-2\log(v/(\pi e)))^2-4)/(8\pi)
$$
in units of $\sqrt{x}$ on $34\le v\le58$. The height is increasing there and stays within $[10^7,H]$ by endpoint checks. For $v\in[l,u]$ in this range we obtain a second $d$ bound
$$
 \left(c(u)+1.000000147+1.78e^{-l/6}\right)
 \left(l^4+\frac{l^3}{1/2-2/34}\right)e^{-l/2}
 +\frac{2}{25}l^5e^{17-l}.
$$
Indeed $c(v)$ increases; bound the earlier integral through 34 by finite RH, and the integral from 34 by the logarithmic derivative of $e^{t/2}/t^2$. All the remaining factors are nonincreasing on this range. ram_early.py takes the minimum with the finite-RH branch, checks blocks of width at most $1/256$, and bridges all improved early cutoffs to the already checked cutoffs in cert.py. For positivity it checks the signed interval $[36.9,39.47]$ and the absolute interval $[39.47,39.7]$. The strict overlap with Lemma 3.4 avoids reliance on the problematic real assertion of the PNT paper.

## 5. What changed

Both contours and pointwise envelopes retain B0. For the numerical reconstruction the change is exactly $S_{27/32}$ added to the minimum in (R3); no other arithmetic or main-term approximation is made more favorable for B1. As an example, $S_{27/32}$ transported by the same operator has a strictly smaller error than the $7/8$ version; it also beats the CH transport for (vge200). To check the latter, the transported $27/32$ contribution is $v^4$ times a positive decreasing exponential mixture (discarding the common early integral and prime-power terms); at 200 it is already below the CH constant floor, as certified by the common bound $S_{27/32}(v)\le 0.3 e^{-5v/32}$ there and the explicit transport factors. Thus both arguments of the analytic gap have improved bounds on (Lge201) in this transport comparison. Onsets and margins in the table compare sufficient certified bounds; they are not lower bounds on what other B0 methods could prove.

The branch determining the exact permanent sign onset is finite and already solved on B0; D02 cannot move this onset left. The early constant-margin losses are controlled by the finite RH/finite arithmetic range, not the new high-exponent input. Intermediate high-order polynomial cutoffs are controlled by the CH plateau switching to the capped-zero density bounds; this is where B1 helps even for some $L<200$, by holomorphic continuation, not by illicitly using the direct estimate on that range. For alternative derivations and their limitations see notes.md.

The leading constant (1) of the normalized gap is optimal **among constant whole-ray margins**: integrating the defining $F'(v)=e^v/v$ by parts six times gives $A(v)=\sum _{j=0}^5 j!/v^j+O(v^{-6})$, with the remainder bounded using the logarithmic derivative of $e^v/v^7$ past a fixed point. The shifted expansion gives $L^4 C(L)=1+14/L+O(L^{-2})$. The B0 spectral transport error tends to zero, so $r(x)\to 1$. This precludes constant margins $>1$; it does not preclude the stronger shaped margins in the table.

The ODE can in principle certify arbitrarily high finite orders by raising the initial point and the working precision. The formal leading residual at order $N+1$ is $g_{N+1}$, which is positive: for (nge6), $\sum _{j=0}^n 1/{nchoose j}\le  2+4/n$, whereas $\sum _{j=0}^n1/j!\ge \sum _{j=0}^4 1/j!>2+4/n$; $n=4,5$ are direct. For fixed $N$, integration by parts to order $N+1$ proves positive initial slack eventually, and an explicit polynomial coefficient test at a sufficiently large start suffices. No uncomputed numerical high-order onset is asserted.
