# Ramanujan gap: exact sign onset and strengthened lower profiles

Write $R(x)=ex\pi(x/e)/L-\pi(x)^2$, $L=\log x$. All endpoints
below are real, with inclusive lower and upper endpoints unless otherwise
specified, and with $\pi(x)=\#\{p\le x\}$. All strict margins are
pointwise, including at jumps. The main portfolio uses B0 of
candidate.md. Section 5 below isolates conclusions not needing QRH
or the proposed additional input.

## 1. Results

**Sharp sign onset, at original finite-computation trust.**
For $N=38358837682$ let $r$ be the unique root on $(N,N+1)$ of
$e r\,632207037/\log r=1644673232^2$. Then $R(r)=0$,
$R(x)>0$ for every real $x>r$, and the least admissible integer
start is $N+1$. The enclosure is
$$38358837682.21792636514465772878
    <r<38358837682.21792636514465772879.$$
Moreover $R(x)\ge67000000(x-r)$ on $[r,N+1]$, and for all $x\ge N+1$
with $n=\lfloor x\rfloor\le e^{58}$,
$$ R(x)>e(x/L-n/\log n)\pi(n/e). $$
The last bound includes integers (where its right side is zero).

**Quantitative whole rays independent of the low Ramanujan check.**
The following table gives strict lower bounds for $L^6 R(e^L)/e^{2L}$
on each entire ray. In particular the .01 margin formerly reported
at $L=39.75$ is now certified from 28.15, and the fixed-margin
tradeoffs include a margin of 1 from 30.8.
   
| log onset | lower profile |
|---:|:--|
|28.15|.01|
|28.35|.10|
|28.65|.25|
|29.15|.50|
|30|.80|
|30.8|1|
|49|$1+14/L+22/L^2$|

Stronger bounded pieces: $1+14/L+20/L^2$ on $[35,43.7]$,
$1+14/L+30/L^2$ on $[49,180]$, and $1+14/L+90/L^2$
on $[50,164]$. Keep the shaped bound below on the whole domain,
including at the joins. For example at fixed onset 58 the uniform
profile above strictly improves inherited A2 ($22$ in place of $4.25$),
and the bounded stronger profile improves the margin further
through $L=164$. The no-density-table margin is $1+3/L$ from 50
(an alternative premise/strength branch).

For higher orders define
$$ a_n=\sum_{j=0}^{n}\binom nj j!-\sum_{j=0}^{n} j!(n-j)!.$$
Thus $a_0,\dots,a_3=0$, and $a_4,\dots,a_{10}=
1,14,145,1412,13985,145450,1610021$. For each ordered pair
\[
 (L_0,k)=(219,3),(253,4),(286,5),(320,6),(355,7),(391,8),
 (426,9),(467,10),(508,11),(552,12),(595,13)
\]
the full lower polynomial $\sum_{j=0}^{k-1}a_{4+j}/L^j$
holds strictly on $L\ge L_0$. In particular the inherited
225/260/330/400 onsets for the first four such polynomials are
all improved. These same numerical polynomial and margin claims also pass using
Dusart alone in the density screen (no FKS Table 8); see ram_dusart_replay.txt.
A truncation with a larger $k$ is stronger on
overlapping rays; the smaller certificates preserve earlier onsets.

**Argument stability.** Put $z=x/e$ and $y=z(1-(1+12/L)/L^4)$.
For all $L\ge58$,
$$ ex\pi(y)/L-\pi(x)^2>.19\,x^2/L^7. $$
This retains and strengthens the inherited A3 branch.

## 2. Repaired prime-count inputs and the shaped bound

The printed finite $\pi$ estimate in FiniteRH Cor. 1 (original
PDF p.4) carries a log-squared power, not the log power used for this
step in D01. Nor can one simply cite full-RH Dudek–Platt Thm 3.1
(PDF p.7) on an asserted finite interval. The current proofs do not
use **either** of these $\pi$ inequalities. They use two lawful replacements:

* FiniteRH Cor. 1 for **theta**, $599<t\le2.169\cdot10^{25}$;
  exactly the log-squared power is needed here. PT2021 Lemma 6,
  PDF p.9, also gives the needed theta bound from 599 to $e^{58}$.
* PT2021 PDF p.8, end of the proof of Cor. 2, explicitly states
  Büt​he's $|\pi(t)-\operatorname{li}(t)|\le\sqrt{t}
  (1.95+3.9/\log t+19.5/\log^2 t)/\log t$ up to $10^{19}$.
  This is a quoted consequence in an allowed original, with original
  computational trust, not a new independent Büt​he input.
  FiniteRH PDF p.5 §3.3 independently records the **sign**
  $\theta(t)<t$ for $2\le t\le10^{19}$, also with that trust.
  The weaker originally used signs up to $1.2\cdot10^{17}$ or
  $1.39\cdot10^{17}$ are not the strongest allowed signs.

Use the PV normalization in this proof and put
$P(L)=\sum_{j=0}^{17}j!/L^j$,
$\ell=P-36e^{1-L}$, $u=P+4Le^{-L}+18!/L^{17}$.
Then $\ell(L)<Le^{-L}\operatorname{li}_{PV}(e^L)<u(L)$ for $L\ge27$.
In fact $0<\operatorname{li}_{PV}(e)<4$: on $[-1,1]$ pair the
positive and negative parts of $e^v/v$, whose integral is between
2 and $e$, and the tail on $(-\infty,-1]$ has absolute value $<1/e$.
Also $0<\operatorname{li}_{PV}(2)<4$ by subtracting
$\int_2^e dt/\log t<(e-2)/\log2<1.1$.
Consequently changing between the two normalizations costs at
most $4Le^{-L}$ in normalized error. This is included in all
uses of PT2021's absolute finite $\pi$ statement.

For the polynomial estimate substitute $v=L-\log t$ in
$\int_e^{e^L}dt/\log t$, and expand $(1-v/L)^{-1}$ through degree 17.
The positive remainder is at most $18!/L^{17}$ since
$1/(1-v/L)\le L$. The missing moment for degree $j$ above $v=L-1$
is at most $e^{1-L}/(1-j/L)$ using $v=L-1+w$,
$(v/L)^j\le e^{jw/L}$. The sum of the latter constants is $<36$
from 27 on (finite arithmetic check). For $L\ge180$, another upper
remainder is $2\cdot18!/L^{18}+Le^{-L/2}$, by splitting at $v=L/2$
and bounding the tail of $(v/L)^{18}\le1$. Take the minimum.

Write $D(L)$ for a bound for $Le^{-L}|\pi(e^L)-\operatorname{li}_{PV}(e^L)|$.
Use the minimum of every applicable entry:
   
1. $D_B(L)=(1.95+3.9/L+19.5/L^2)e^{-L/2}+4Le^{-L}$
   on $27\le L\le43.7$, by PT2021 and the normalization guard.
2. $D_f(L)=(L^2+2L)e^{-L/2}/(8\pi)+1354Le^{-L}$ for $27\le L\le58$.
   Indeed,
   $\pi(x)-\operatorname{Li}_2(x)=(\theta(x)-x)/L+
   \int_2^x(\theta(t)-t)/(t\log^2 t)dt+2/\log2$.
   Above 599 cancel the two log powers under the integral;
   below 599 use $|\theta(t)-t|\le t$ (Dusart Thm 4.2, k=0,
   PDF pp.11–12) and $\log2>2/3$. The prefix and change of
   normalization together cost $<1354$ in unnormalized units.
3. Let $A_0=\pi/(3\cdot10^{12})$ (not the hypothetical assumption),
   $u_c=A_0+117e^{-L/2}$, and
   $$ h_c(L)=A_0/(.9L)+117e^{-L/2}/(.4L)+3Le^{10-L}.$$
   The bound $D_c=u_c+h_c$ works from 27 on. To see this subtract
   the exact theta boundary term in the preceding formula and
   propagate the remaining error via the integral starting at $a=20$.
   At $a$, the preceding proof gives residual at most
   $2a e^{-a/2}/(8\pi)+1354a e^{-a}<3a e^{10-a}$, since it
   excludes the theta boundary term. CH2 Cor. 1.3 (PDF p.3)
   and Dusart Cor. 4.5 (PDF p.13) give $u_c$ for relative theta.
   For each exponential $K e^{-\eta t}$ in the relative theta
   error integrate using
   $(e^{(1-\eta)t}/t^2)'\ge(1-\eta-2/a)e^{(1-\eta)t}/t^2$.
4. For $L\ge180$ set $D_p=C(L)e^{-L/8}+3e^{-L/2}+\min(h_c,h_p)$,
   where
   $$h_p=\frac{.01361e^{-L/8}}{L(7/8-2/180)}
           +\frac{3e^{-L/2}}{L(1/2-2/180)}
           +7\cdot10^{-15}(L/180)e^{180-L}.$$
   The same integral from 180 works since $h_c(180)<7\cdot10^{-15}$
   and $C(t)<.01361$ thereafter. One can instead integrate the
   exact bound $\min(u_c(t),C(t)e^{-t/8}+3e^{-t/2})$ pointwise
   on the part above 180; the residual formula is explicit
   and only decreases the error.
5. The density-free direct majorant for $L\ge200$ gives
   $$D_d(L)=\frac{(L^2+8L/7)e^{-L/8}}{64}
   +3e^{-L/2}\left(1+\frac{1}{L(1/2-1/100)}\right)
   +7\cdot10^{-15}(L/200)e^{200-L}.$$
   The $t^2$ in the majorant cancels the denominator in the
   anchored integral. Here one may use either the actual contract
   or the B0 QRH proof of it from candidate.md.
6. **Oscillation-aware prefix.** For $a=20$ and the coarse
   smoothed bound $j(L)=.04620e^{-L/2}+2e^{-L}+7\cdot10^{-12}e^{-L/8}$
   proved in mertens_current.md, put
   $$
   h_s(L)=\left(3a e^{10-a}+j(a)/a\right)(L/a)e^{a-L}+j(L)/L
     +\frac{3.04620 e^{-L/2}}{.4L}
     +\frac{7\cdot10^{-12}e^{-L/8}}{.775L}
     +\frac{2L}{a}e^{-L}.
   $$
   One may replace $h_c$ in $D_c$ at $L\ge58$ by $\min(h_c,h_s)$
   and replace the residual of $D_p$ by $\min(h_c,h_s,h_p)$.
   Indeed $J_1'=-e_\psi$ off jumps, and it is locally absolutely
   continuous. Integrate by parts in the anchored integral with
   $G(t)=e^t/t^2$; $0\le G'\le G$. Bound the two boundary terms by
   $j(L)/L$ and $(L/a)e^{a-L}j(a)/a$ after normalization.
   For the remaining integral use the same exponential derivative
   bound as before, adding $3e^{-t/2}$ for $\psi-\theta$.
   The trivial $2e^{-t}$ term integrates against $G$ to at most
   $2/a$ before normalization. This avoids propagating a constant
   CH2 error through the prefix at the spectral handoff.
7. If desired for $L\ge2000$ include
   $235 L^{1.52}e^{-.8\sqrt L}+4Le^{-L}$ (PT2021 Cor. 2, PDF p.2,
   converted from $\operatorname{Li}_2$), and the QRH-free $E_U$
   and $E_C$ bounds below, also adding $4Le^{-L}$ when converting.

For a one-sided upper bound on the squared factor, use
$D_+(L)\le 3Le^{-L}$ throughout $[28,43.7]$ in addition to $D_+\le D$:
the theta sign from FiniteRH §3.3, in the partial summation formula
with $\operatorname{Li}_2$, gives the result for PV as
$\operatorname{li}_{PV}(2)>0$. It does not require a finite
$\pi-\operatorname{li}$ sign claim or a normalization convention
for the latter. The checker uses this saving through 43 and
ignores it afterwards. By bounding $\pi$ at both arguments we get
the strict shaped lower bound, with $\ell$ and $u$ as above,
$$
R(x)>\frac{x^2}{L^2}\left[
    \frac{L}{L-1}\{\ell(L-1)-D(L-1)\}-(u(L)+D_+(L))^2
                    \right]\qquad(L\ge28).
$$
This formula is valid even if its right side is negative.
A shaped upper comparator follows by reversing which $\pi$ endpoints
are used (clip the lower bound for $\pi(x)$ at zero before squaring).
It is important not to omit stronger independently derived branches
when two curves cross.

## 3. Entire-domain margin proof

Expand $L P(L-1)/(L-1)$ using positive binomial series in $1/L$.
Compare coefficients through degree 17 with $P(L)^2$. Those through
degree 3 cancel; the rest are positive. Thus the strict normalized main
gap is bounded below by $\sum_{j=0}^{13} a_{4+j}/L^j-\epsilon(L)$,
where $\epsilon$ overbounds the omitted square coefficients, the change
from $P$ to $u$ in the square, and the change from $P$ to $\ell$
at $L-1$. Explicitly, if $d_0=u-P$ so that the choice of the smaller
remainder is allowed,
$$
\epsilon(L)=\sum_{\substack{0\le j,k\le17\\j+k\ge18}}
     \frac{j!k!}{L^{j+k-4}}
     + L^4\left\{(2P+d_0)d_0+\frac{36L}{L-1}e^{2-L}\right\}.
$$
Subtract
$L^4\{L D(L-1)/(L-1)+(2u(L)+D_+(L))D_+(L)\}$
for the count losses. On every closed cell $[l,r]$ the checker
evaluates decreasing factors at $l$, reserving a domain-dependent
estimate only if the **entire** cell (shifted by 1 where appropriate)
is in domain, and evaluates positive scaling powers of $L$ and
the decreasing positive main polynomial at $r$. This certifies
every interior point, not just $l$ and $r$.
For a coefficient of offset $k$ subtract the first $k$ terms and
scale by $L^k$, so the next main coefficient is constant and the rest
are positive. The latter scaled losses decrease on the stated
infinite tail: expand positive terms; for factors
$L^i(L-h)^j e^{-c(L-h)}$ with $h=0,1$ the positive log
derivative is at most $i/L+j/(L-h)<c$ on the ray where used.
For the spectral loss the fastest possible positive factors have
$i\le17,j\le1,c\ge1/8$ at $L\ge188$; the direct-input loss uses
$i\le5,j\le2,c\ge1/8$ at $L\ge275$. Inverse-power losses in
$\epsilon L^k$ are nonincreasing for $k\le13$; the elementary
exponential factors also decrease there. Reciprocal positive factors
and $L/(L-1)$ are decreasing. These arguments bound the entire
last ray by one directed check of the first omitted coefficient;
the intermediate $22/L^2$ profile checks $a_6-22$ instead.
For the density-free branch use CH2 through 275 and $D_d$ thereafter.
No cutoff analysis outside a tested domain is used.

For the stability claim, $\log y\ge L-1.001$ by the endpoint check
at 58 and monotonicity. Subtracting the logarithmic integral at $z$
and $y$ costs at most $(z-y)/\log y$; in units $x^2/L^6$ this is
$<(1+13.23/L)$ from the displayed shrink factor.
The two possible prime-count residuals cost at most
$2L^5D(L-1.001)/(L-1.001)$, using their monotone majorants.
To bound this by $.58/L$ on $[58,188]$ evaluate the
$L^5$-scaled constant part of $D_c$ at 188 and its decreasing tails
at 58, with $L/(L-1.001)\le58/(58-1.001)$.
Beyond 188 both arguments are covered by the spectral bound
and the $L^6/(L-1.001)$-scaled terms decrease.
These checks and the strict $1+14/L+22/L^2$ reserve give the .19 claim.

## 4. Exact low real join

PT2021 Thm 2 (PDF p.3; §5 pp.9–11) supplies positivity for the
**integers** $N<n\le e^{58}$ at original numerical trust. Its literal
unrestricted-real lower edge cannot be used: the endpoint check
independently certifies $\pi(N)=1644673232$,
$\pi(N/e)=632207037$ and that the counts remain constant on
$[N,N+1]$. Specifically $N+1$ is composite and the floor of $x/e$
is the same at both ends. The quotient-sieve proof is in
historical_d02_candidate.md §Ramanujan conclusions: decreasing
updates remove exactly multiples of the current least prime factor
and the quotient set is closed under floor division. The elementary
monotonicity of $x/\log x$ and strict numerical bracket prove
the exact root, including failure at $N+.1$ and equality at $r$.
The derivative lower bound is checked at both ends by
endpoint_check.py. For $n=\lfloor x\rfloor\ge N+1$,
the inequality displayed in §1 follows by positive integer $R(n)$,
monotonicity of $\pi(x/e)$, and $\pi(x)=\pi(n)$. The analytic
margin from $e^{28.15}<e^{58}$ overlaps fully; there is no missing
real interval. This method does not redo the whole published low
integer verification. Dudek–Platt Thm 1.3 (PDF p.2) is a separate
full-RH result about **integers**, not an input of full RH here.
Their Thm 1.2 gives the older $L\ge9658$ positivity ray,
subsumed by PT2021's large ray $L\ge3915$; the new profile is
strictly stronger throughout those domains.

## 5. QRH-free secondary frontier

The low margins through $L=180$ also have QRH-free proofs: omit $D_p$
and the optional smoothed residual (prefix_replay.txt). The earlier D01 single-branch
secondary estimates and the independently replayed C014 intervals
below are not tied to the new smoothed handoff.
Keep separately the exact original historical C014 conclusion
$R(x)>.03x^2/L^6$ from $L=2840$, and the middle interval
$R(x)>.004x^2/L^6$ on $[169,753]$ from the same archive.
The upper proof is historical_d02_extensions.md, LF40–108,
with its normalized $E_U$ and polynomial argument from
historical_d02_candidate.md LF18–34 and LF88–113. The
CH2 branch $E_C$ comes from the latter's partial-summation
split and is used in the middle interval. Replay the
QRH-free functions high_unconditional and signed_small_ramanujan
from extra_check.py. See secondary_replay.txt. The fixed
upper claim is at written/source plus ordinary rational replay
tier; it uses Dusart Thms 2.3–2.4 (PDF p.5), FKS Thm 3.2
and Cor. 1.4, plus the paper-backed finite RH verification.
It uses a single height-dependent decreasing weight for the
density and zero-free region, and certified upper rectangles
before the analytic FKS tail. It is neither a new consequence
of the contract nor a source-first PV result. The resulting QRH-free positivity domain contains
$(r,e^{753}]\cup[e^{2840},\infty)$. No QRH-free
bridge of $753<L<2840$ is asserted here. In B0 the QRH-based
profile fills it with a stronger margin.
