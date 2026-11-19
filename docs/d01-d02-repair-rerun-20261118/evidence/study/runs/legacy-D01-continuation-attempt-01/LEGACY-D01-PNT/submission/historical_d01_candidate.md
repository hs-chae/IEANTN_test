# Explicit Ramanujan and Mertens estimates $A-D01$

All bounds are for real arguments, use right-continuous prime counts, and use natural logarithms. Put $L=\log x$. Results are derived from the given **hypothetical** PsiMajorant and the specified original-source inputs. No full RH is assumed. The paper-backed finite RH and tables keep their original trust status. See `sources.md`; numerical certificates use integer arithmetic $`rigor.py`, `analytic_check.py`, `count.py`$.

## Selected results and file map

* **Ramanujan:** R1 below gives the optimal real sign endpoint, and
  (A2) in **refined.md** supersedes the simpler R2 margin, giving
  $R(x)>x^2/L^6(1+14/L+4.25/L^2)$ throughout $L\ge58$,
  with further asymptotic polynomials, a shaped bound and a
  shifted-argument stability result. The density-free route is retained.
* **Mertens:** the selected whole-ray curve is the pointwise
  minimum of the certified bands in **finite.md** and the analytic
  inequalities in **refined.md**, Section B, wherever each applies.
  This improves the original constants on all their full domains,
  extends to (300000) at larger constants, and ultimately saves
  a power of $x$. The values and reproduction details are in the
  finite and analytic certificates.
* **Tertiary:** Section C of **refined.md** proves a normalized
  primorial extremal bound and a prime abundance result for
  intervals of length $x^{5/8}(\log x)^{14}$; this last result
  uses cancellation of identical zero contributions rather than
  subtraction of unsigned endpoint errors.

## Initial analytic results, retained proofs and R1

**R1 (optimal real sign endpoint, using the paper-backed finite interval in its integer form).** Put $n_0=38358837682$ and let $r$ be the unique solution in $(n_0,n_0+1)$ of
$$
 \frac{e r}{\log r}\,632207037=1644673232^2.
$$
Then $R(x)>0$ for every $x>r$, and $R(r)=0$. In fact
$$
 n_0+\frac{2179}{10000}<r<n_0+\frac{218}{1000}.
$$
Thus the smallest open real-ray endpoint is $r$, and the smallest integer start is $n_0+1$. This bridges the entire published gap from $e^{58}$ to $e^{3915}$. The literal finite **real** endpoint in Platt--Trudgian Thm. 2 is contradicted on ($n_0,r]$; the published positivity at integers $n_0<n\le e^{58}$ is retained (see source qualification below). We do not use the false open segment as a premise.

**R2 (quantitative, independent of the published low Ramanujan verification).** For $L\ge58$,
$$
 R(x)>\frac{x^2}{L^6}\le ft(1+\frac{12}{L}\right).
$$
This is a strict positive margin on the entire old ray. The following sharper, shaped bound holds for $Lin[37,39]cup[40,\infty$) (and as a lower bound even whenever the expression there is negative):
$$
 R(x)>\frac{x^2}{L^2}
 \le ft[\frac{L}{L-1}{\ell(L-1)-D(L-1)}
             -{u(L)+D_+(L)}^2\right].                    \tag{R}
$$
Here use $D_+=0$ on $[37,39]$ and $D_+=D$ otherwise. Definitions of (ell,u,D) are below; the bracket is positive throughout the stated range. One can take the maximum with the simpler bound when both apply. If one avoids the FKS density table, a separate proof gives $1+3/L$ in place of $1+12/L$, on the same ray starting at $e^{58}$. In particular R1 does not need the FKS density table or the OpenAIQRH theorem.

**M1 (reciprocal products and prime sums).** Define
$$
 \begin{split}
 S_0(x)&=\sum_{p\le x}1/p,\quad S_1(x)=\sum_{p\le x}(\log p)/p,\\
 K_0(L)&=(1+L^{-1})/L,\\
 j(L)&=.11 e^{-L/2}+2e^{-L}+7\cdot10^{-12}e^{-L/8},\\
 d(L)&=(1.41+2.4/L)e^{-L/2}/L,\quad b(L)=1.41e^{-L/2},\\
 v(L)&=E(L)/L+2K_0(L)j(L),\qquad w(L)=E(L)+j(L).
 \end{split}
$$
Take the following admissible (E), or the pointwise minimum of any admissible estimates below:
$$
 E(L)=
 \begin{cases}
 L^2 e^{-L/2}/(8\pi) &21\le L\le58,\\
 \pi/(3\cdot10^{12})+113.67e^{-L/2}&58<L<190,\\
 J(L)+B(L)&190\le L ,
 \end{cases}                                                \tag{E}
$$
where the explicit finite-sum (J+B) is in Section 1. For **all** $L\ge21$,
$$
 \begin{array}{rcl}
 -v(L)&\le&\log(e^{-\gamma}Q(x)/L)\le v(L)+d(L),\\
 -v(L)&\le&S_0(x)-\log L-M\le v(L)+d(L),\\
 -w(L)&\le&S_1(x)-L+B_3\le w(L)+b(L).
 \end{array}                                                \tag{M}
$$
In particular both relative product errors are $\le\exp(v+d)-1$. The individual upper errors for (Q) and (P) can be taken to be $e^{v+d}-1$ and $e^v-1$, and the individual lower deficits $1-e^{-v}$ and $1-e^{-v-d}$, respectively. For every $L\ge22$, both absolute relative product errors and the $S_0$ absolute error are $<.170/L^3$, in place of $.2/L^3$. For $L\ge21$, the $S_1$ absolute error is $<.235/L^2$, in place of $.3/L^2$. These comparisons hold on full rays, not just samples. The original Dusart estimates are retained before these crossovers. With (E) (M) is $O(x^{-1/8}/\log x)$ for $P,Q,S_0$, and $O(x^{-1/8})$ for $S_1$.

### 1. Power estimate and inputs

Let $C(L)=|psi(e^L)-e^L|/e^L$. The finite-RH bound, the CH2 bound and the hypothetical input bound $C(L)$, respectively, by $L^2 e^{-L/2}/(8\pi)$ for $59<e^L\le2.169\cdot10^{25}$, by $A+113.67e^{-L/2}$ for $L\ge0$, and by $L^2 e^{-L/8}/64$ for $L\ge200$, where $A=\pi/(3\cdot10^{12})$. These are admissible for the minimum in (E). The input also implies $\betale7/8$: for $\Re s>1$, unique factorization, absolute convergence and summation by parts give
$$
 -\zeta'(s)/\zeta(s)=s/(s-1)+s\int_1^\infty(psi(t)-t)t^{-s-1},dt.
$$
The latter integral is locally normally convergent on $\Re s>7/8$ by the input, ruling out zero poles there by the identity theorem (away from $s=1$). Alternatively OpenAIQRH Thm. 1.1 gives the same strip in the admitted corpus. A real nontrivial zero does not occur because, for real $0<s<1$, the alternating series $(1-2^{1-s})\zeta(s)=\sum_{n\ge1}(-1)^{n-1}n^{-s}$ is positive; continuation of the identity follows by locally uniform convergence of the paired series on $\Re s>0$.

Here is a screened-zero bound improving the given coefficient, polynomial and onset. Set $H_0=3\cdot10^{12}$, $h=\log H_0$, $s_i=(770+i)/1000$ for $0\le i\le105$. Use the (c,d) in `analytic_check.py`, which round up the FKS Cor. 2.9 Table 8 entries on the containing intervals. Define
$$
 W(s,z)=2\le ft[\frac{c, e^{-\lambda z}z^q}{\lambda-q/z}
           +\frac{d,e^{-z}z^2}{1-2/z}\right],
 \qquad \lambda=(8s-5)/3,\quad q=5-2s.
$$
For (zge h) this bounds $2\sum_{\betage s,\gamma\ge e^z}1/\gamma$: integrate the counting upper bound against $du/u^2$ from $e^z$ to infinity, dropping the nonpositive lower endpoint term in Stieltjes summation. The integral after $u=e^t$ is bounded by its starting value divided by the negative logarithmic derivative there, which decreases the integrand at least exponentially (the log derivative is decreasing). This also covers a zero with ordinate precisely $e^z$. By finite RH all $\beta>1/2$ have $|\gamma|>H_0$.

Let $w_i=W(s_i,h)$ for $0\le i<105$ and $w_{105}=0$. The checker verifies strict decrease. Put
$$
 \begin{split}
 B(L)&=\sum_{i=0}^{104}(w_i-w_{i+1})e^{-(1-s_{i+1})L},\\
 J(L)&=2.1L e^{-L/3}+(z_*^2/6+3)e^{-L/2}
                 +(z_*^2/12+1)e^{-.23L}+e^{-L/8}W(.77,L/3),
 \qquad z_*=L/3+1.
 \end{split}
$$
For $L\ge190$, apply the signed FKS Thm. 3.2 with $T=e^{L/3}$, $T^*in[T,2.45T]$, $\alpha=1/2,\omega=0,M=2.091,\log x_M=40$. The domain inequalities hold at 190 and are preserved by exponential growth (or directly $T> L$ and $e^{L/2}/e^{L/3}=e^{L/6}$). The terms from $\betale1/2$ have total absolute value, divided by $x$, at most $(z_*^2/6+3)e^{-L/2}$. Indeed use twice FKS Table 1 at $U=100$ plus $2B_1(100,T^*)$, in which the prefactor in (2.1) is $<1/6$ and the final correction $<.9$ (sharper $<.1$ at 100, verifiable directly). The log product there is bounded by $(z_*^2-(\log U)^2)/2$. For $1/2<\beta<.77$, symmetry in the critical line bounds twice the positive-ordinate reciprocal sum by $B_1(H_0,T^*)$, giving $(z_*^2/12+1)e^{-.23L}$. All remaining zeros lie between .77 and .875. The absolutely convergent complete sum of these high-strip terms, divided by $x$, is bounded by $B(L)$: round each real part up to the next grid point, bound the cumulative masses by $w_i$, and sum the positive differences of the resulting increasing weights. The omission above the cutoff is bounded by the $W(.77,L/3)$ term of (J). Consequently
$$
 C(L)\le J(L)+B(L)<.023e^{-L/8}\quad(L\ge190).               \tag{PS}
$$
Each term of $e^{L/8}(J+B)$ decreases weakly on that ray (positive polynomial times strictly decaying exponential, or (W) with $z$ increasing, or nonnegative weight times decreasing exponential). Its starting value is $<.022$ $in fact enclosed near .021768$. Thus $PS$ strictly improves $L^2/64$ for all $L\ge200$ and starts ten logarithmic units earlier. The leading coefficient of (J+B) is $w_{104}=W(.874,h)$. The error gain comes from absolute summability in a **high strip**, not from assuming absolute summability of the full unsmoothed zero sum.

### 2. Prime count and Ramanujan gap

Write $\mathcal A(L)=L e^{-L}\operatorname{li}(e^L)$, with principal-value normalization. Use $P_{17}(L)=\sum_{k=0}^{17}k!/L^k$ and
$$
 \ell(L)=P_{17}(L)-36e^{1-L},\qquad
 u(L)=P_{17}(L)+4Le^{-L}+18!/L^{17}\qquad(L\ge36).
$$
Then $\ell<\mathcal A<u$. Indeed $0<\operatorname{li}(e)<4$: substitute $v=\log t$ in the PV, then integrate $(e^v-e^{-v})/v$ on $[0,1]$ and $e^v/v$ on ($-\infty,-1]$. The first integral lies between 2 and $e$, and the second between $-1/e$ and 0. Expand the geometric factor in $\mathcal A=Le^{-L}\operatorname{li}(e)+\int_0^{L-1}e^{-v}/(1-v/L),dv$ through degree 17. The positive remainder is bounded by $L\cdot18!/L^{18}$; the missing tails in the moment integrals are at most $e^{1-L}\sum_{k=0}^{17}(1-k/L)^{-1}<36e^{1-L}$ (translate $v$ by $L-1$ and use the finite binomial expansion).

For the normalized absolute prime-count error $\delta(L)=Le^{-L}|\pi(e^L)-\operatorname{li}(e^L)|$, use the minimum of the following at each argument:
* $D_f=L^2 e^{-L/2}/(8\pi)$, for $20\le L\le58$.
* For $L\ge20$,
$$
 D_c=A(1+1/(.9L))+117e^{-L/2}(1+1/(.4L))+
                   40Le^{10-L}/(8\pi).
$$
* For $L\ge190$ use
$$
 D_d=.023 e^{-L/8}{1+1/[L(7/8-2/190)]}
    +3e^{-L/2}{1+1/[L(1/2-2/190)]}
    +2.12\cdot10^{-12}(L/190)e^{190-L}.
$$
* For $L\ge200$ one may alternatively use
$$
 D_h=(L^2+8L/7)e^{-L/8}/64+
     3e^{-L/2}{1+1/[L(1/2-2/200)]}
       +2.12\cdot10^{-12}(L/200)e^{200-L}.
$$

To derive these, $\theta(y)\le2y$ for $y\ge1$ $Dusart Thm. 4.2, (k=0)$; for $L\ge20$, split $psi-\theta=\sum_{k\ge2}\theta(x^{1/k})$ at $k=2,3,4$ and bound $k\ge5$ by $2x^{1/5}L/\log2$. This gives $0\le psi-\theta<3\sqrt x$ (the extra three terms divided by (sqrt x) are decreasing and total $<1$ at 20). Let $F(L)$ bound $|\theta(e^L)-e^L|/e^L$. The anchored summation bound for (Lge a) is
$$
 \delta(L)\le F(L)+L e^{-L}\int_a^L e^t F(t)/t^2,dt+
 (L/a)e^{a-L}{\delta(a)+F(a)}.
$$
For a term $K e^{-eta t}$ the integral contribution is at most $K e^{-eta L}/[L(1-eta-2/a)]$ by differentiating $e^{(1-eta)t}/t^2$; for the input term $t^2 e^{-t/8}/64$, integrate explicitly. For $D_c$ use $a=20$, finite-RH $\theta,\pi$ at anchor and $F(t)=A+117e^{-t/2}$ after anchor. For the other two use that last majorant and $D_c$ at the anchor, so their sum is $<2.12\cdot10^{-12}$ as tested. After anchor use $PS$ or the input plus $3e^{-t/2}$. At $L\le39$ we can also use $\pi(e^L)\le\operatorname{li}(e^L)$ as reported by Dudek--Platt p. 8, since $e^{39}<1.2\cdot10^{17}$. This last source computation is not needed for $L\ge40$.

Now apply the lower bound to $\pi(x/e)$ and upper to $\pi(x)$; the positive upper bound can be squared. This gives (R). To verify positivity and the uniform margins, the normalized main gap with (ell,u), multiplied by $L^4$, exceeds
$$
 \mathcal P(L)-\varepsilon(L),\qquad
 \mathcal P(L)=\sum_{k=4}^{17}
 \frac{\sum_{j=0}^k \binom{k}{j}j!-\sum_{j=0}^k j!(k-j)!}{L^{k-4}} .
$$
Indeed expand $\frac{L}{L-1}P_{17}(L-1)$ with the binomial series, keeping degrees 0 through 17, and subtract $P_{17}(L)^2$. The first four differences vanish; the next three are $1,14,145$, and the remaining kept coefficients are positive. The upper bound on the omitted square and cutoff losses $\varepsilon$ is computed explicitly by `maincmp`; both $\varepsilon$ and $L\varepsilon$ decrease on $L\ge37$, termwise after multiplication out (each is a sum of decreasing products $L^{-m}$, (L^j e^{-
u L}), and $L/(L-1)$, or their products with positive coefficients). $\varepsilon(37)<.0001$.

The scaled prime-count loss is
$L^4[D_+(L)(2u(L)+D_+(L))+\frac{L}{L-1}D(L-1)]$.
For $D_f$ this decreases on $[37,58]$ by differentiating $L^j e^{-L/2}$ and $L^5(L-1)e^{-L/2}$, and the factors $u,D_f$ decrease. Compare at endpoints of $[37,37.1],[37.1,38],[38,39],[40,41]$; on $[41,58]$ it is $<.91$, below $1-.0001$. For $58\le L\le191$, use $D_c$, bound its constant component (including $1/(.9L)$) at $L-1=57$ and scale by $191^4$, and the remaining scaled decaying factors at 58 (or 57 for their shift); the result is $<.01$. For $L\ge191$, use $D_d$ also at $L-1$. Even after scaling by $L^5$ rather than $L^4$, the loss is decreasing: each term is built from $L^j$ with $j\le6$, $L/(L-1)$, decreasing reciprocal factors, and exponentially decreasing factors of rates at least $1/8$; a shifted linear factor is absorbed using $L/(L-1)$ or bounded via (L) exactly. The starting scaled-by-$L^4$ value is $<.01$. In both ranges the total loss including $\varepsilon$, scaled by $L^5$, is therefore $<191(.01)+37(.0001)<2$. This proves the $12/L$ margin. For the density-free variant switch at 271 to $D_h$. The analogous scaled-by-$L^4$ bounds are $.03,.05$, respectively; more sharply the latter is $<.038$ at 271. Scaled-by-$L^5$ losses decrease after 271 $\maximal polynomial degree 7$; $271(.038)+37(.0001)<11$, proving the $3/L$ margin.

**Endpoint certificate and the original claim.** `count.py` uses the quotient sieve on the closed set of distinct (lfloor n/j
floor): initially count integers $\ge2$ up to each quotient. When a new prime (plesqrt n) is found by differencing the counts at $p,p-1$, remove $p$ times surviving integers (ge p) at each quotient $\ge p^2$, in decreasing order, leaving $p$ itself. This inductively removes exactly the composites with least prime factor $p$; (lfloorlfloor n/j
floor/p
floor=lfloor n/$jp$
floor) supplies the closure. The certificate checks both counts and the constancy of both over $[n_0,n_0+1]$ (including composite $n_0+1$); exact interval arithmetic encloses the sign on either side of $r$. On $[n_0,n_0+1]$, (R) is strictly increasing because (x/log x) is. On $[n_0+1,e^{58}]$, use the **integer** restriction of the paper-backed positivity and (R$x$ge R(lfloor x
floor)) for $x>e$ (same $\pi(x)$, other factors nondecreasing). Beyond this our quantitative lower bound applies. For any noninteger $x\ge n_0+1$ with (lfloor x
floorle e^{58}) one also gets the strict lower margin (e(x/L-lfloor x
floor/loglfloor x
floor)pi(lfloor x
floor/e)); on ($r,n_0+1]$ the formula for (R) is exact. The numerical root certificate does not independently verify the billions of other low-range comparisons in the original paper.

### 3. Smoothed error and Mertens

Put $e_psi(t)=(psi(t)-t)/t$, $J_1(x)=\int_x^\infty e_psi(t),dt/t$. The key improvement over unsigned integration is
$$
 J_1(x)=\sum_\rho\frac{x^{\rho-1}}{\rho(\rho-1)}
          -\frac{\log(2\pi)}{x}+\sum_{m\ge1}\frac{x^{-2m-1}}{2m(2m+1)}
 \quad(x>1).                                                \tag{J}
$$
For rigor, this is obtained by integrating the Perron kernel before any sum over zeros: with $A(s)=-\zeta'/\zeta(s)$, integrate $A(s)x^{s-1}/[s(s-1)]$ on $\Re s=2$, divided by $2\pi i$. The kernel $\int y^s/[s(s-1)],ds/(2\pi i)=(y-1)_+$ follows by residues, including continuity at $y=1$. Absolute convergence permits termwise integration of the Dirichlet series, giving $\int_1^xpsi(t)dt/t^2$. Shift to the line $\Re s=-2m-1$. Here are details for the limiting shift: $B.9$ of CH2, compared at $s=\sigma+iT$ and $2+iT$, gives $A(s)=O_m(\log^2 T)$ for $-2m-1\le\sigma\le2$ along heights $T\toinfty$ separated by $\gg1/\log T$ from all ordinates. Such heights exist in each interval $[n,n+1]$ since FKS Lemma 2.1 and Remark 2.2 give $O(\log n)$ zeros in $[n-1,n+2]$, so exclude small intervals of total length $<1$. In $B.9$, the terms with $|T-\gamma|\le1$ are $O(\log^2 T)$ in total; farther paired differences are bounded by $O_m\big(\sum_{|\gamma-T|>1}|T-\gamma|^{-2}\big)=O_m(\log T)$, using the same unit-bin count and $\sum_{j\ge1}\log(2+j)/j^2<\infty$. The digamma terms are $O_m(\log T)$ by CH2 $A.5$ and the recurrence (or $A.4$ in the left half-plane). Thus horizontal integrals vanish. On the left odd-integer line $A.3$, with bounded cotangent there and $1-s$ in $\Re\ge2$, gives $A(s)=O(\log(2+|s|))$ uniformly in $m$; its integral is $O(x^{-2m-2}\log(2+m)/(1+m))$. The residues are (L+c) at 1 (constant $c$ independent of $x$), $+\log(2\pi)/x$ at 0, and negatives of the displayed zero and trivial-zero terms. The value $\zeta'/\zeta(0)=\log(2\pi)$ also follows from $A.2$: the simple pole at 1 has constant $\gamma$ (integral comparison of the zeta series with its integral); $\Gamma(1)=1,\Gamma'(1)=-\gamma$ (Euler's gamma product), so the linear terms from those two factors cancel. Equivalently the constant in Dusart (2.1) is this residue. Both residue series converge absolutely by the zero counting bound. Subtract (L), let $x\toinfty$ using the strip and summable coefficients, and subtract the finite-$x$ formula from its limit to obtain (J). No interchange with the unsmoothed conditionally convergent zero sum is used.

By CH2 Cor. B.2 and partial summation,
$2\sum_{\gamma\ge T}\gamma^{-2}\le 2(\log(T/(2\pi))+1)/(\pi T)$ for $T\ge2\pi$. The FKS Table 1 reciprocal sum below 100 and first ordinate $>14$ $CH2 PDF p. 43$ give $2\sum_{0<\gamma<100}\gamma^{-2}\le2(.5922435112)/14$. Together these bound the total absolute weights $1/|\rho(\rho-1)|$ by .11. Above $H_0$ the corresponding sum is $<7\cdot10^{-12}$. Below $H_0$ use finite RH; above it use $\betale7/8$. The trivial terms in (J) with $-\log(2\pi)/x$ have joint absolute value $<2/x$ for $x\ge2$ (bound the positive series by $x^{-3}/[6(1-x^{-2})]$). Hence $|J_1(e^L)|\le j(L)$. For the logarithmic kernel,
$$
 \le ft|\int_L^\infty e_psi(e^t)K_0(t),dt\right|
 \le K_0(L)j(L)+\int_L^\infty(-K'_0(t))j(t)dt\le2K_0(L)j(L).
$$
This is a smoothing of the tail, not of the prime-count jump at $x$.

For $i=0,1$, set $U_0=\sum_{n\le x}Lambda(n)/(n\log n)$ (the $n=1$ term is omitted) and $U_1=\sum_{n\le x}Lambda(n)/n$. Abel summation from $x$ to infinity gives
$$
 U_0-\log L-\gamma=e_psi(x)/L-\int_L^\infty e_psi(e^t)K_0(t)dt,
 \qquad U_1-L+\gamma=e_psi(x)-J_1(x).
$$
The constants are fixed by Dusart Thms. 5.6--5.7 and their definitions of $M,B_3$, since the total power corrections are absolutely convergent and their tails tend to zero. Specifically, $\log Q=U_0+\sum_{p\le x, p^k>x, k\ge2}1/(kp^k)$;
$S_0-\log L-M=U_0-\log L-\gamma+D_0$ with $D_0=\sum_{p^k>x, k\ge2}1/(kp^k)$;
$S_1-L+B_3=U_1-L+\gamma+D_1$ with $D_1=\sum_{p^k>x, k\ge2}\log p/p^k$.

For $L\ge21$, one has $.99\sqrt x<psi(x)-\theta(x)<1.2\sqrt x$: use Dusart Thm. 4.2 with $k=3,eta_3=10$ for (sqrt x) and the same crude $k\ge3$ terms as above. At $L=21$ the required extra terms are checked in the certificate and they decrease thereafter. Partial summation against $1/x$ and $1/(x\log x)$, including the negative boundary term at $x$, now gives $0\le D_1\le b(L)$ and $0\le D_0\le d(L)$ (in the latter integral, bound $K_0(t)\le K_0(L)$). These statements use (le x) versus $>x$, even at jumps. This proves (M).

For the whole-ray baseline comparison $e^y-1\le y/(1-y)$ for $0\le y<1$. On $[22,58]$ both $L^3(v+d)$ and (v+d) decrease termwise, using the first branch of (E); the scaled majorant at 22 is $<.170$. For the weighted prime sum use the same reasoning on $[21,58]$, with starting scaled bound $<.235$. On $[58,190]$ use CH2, bounding the constant contribution to either scaled error by $190^2 A<4\cdot10^{-8}$ and all exponential terms by their scaled values at 58. The result (including the product exponential) is $<.002$. On $[190,\infty$) bound (E) by $PS$; scaled errors decrease termwise, with starting bounds $<.001$. This proves the strict comparisons with the displayed Dusart baselines. The estimates in (M) themselves use the certified tighter shape rather than these comparison surrogates.
