# Ramanujan: real endpoint, upper and lower estimates for π, connected profiles

All assumptions are B0 as in candidate.md. Use right-continuous \(\pi\), natural logarithms and principal-value \(\mathrm{li}\) (Dusart §5.1, PDF pp. 13–14). The sign and profile inequalities are strict.

## Statements and tradeoffs

Let \(n=38358837682,\ m=14111427770,\ b=632207037,\ c=1644673232\). There is a unique \(r\in(n,n+1)\) satisfying \(ebr/\log r=c^2\), with
\[
 \frac{164749953357698434483}{4294967296}<r<
 \frac{41187488339424608621}{1073741824}.
\]
One has \(R(r)=0\), \(R(x)<0\) for \(n\le x<r\), and \(R(x)>0\) for every \(x>r\). More locally \(R(x)>67000000(x-r)\) for \(r<x\le n+1\). Hence \(r\) is the last real counterexample and \(n+1\) the first integer of the connected positive ray.

The normalized margin \(R(x)L^6/x^2\) is strictly above every applicable entry:

| Closed domain in \(L\) | Lower profile |
|---|---:|
| \([36.54,\infty)\) | .005 |
| \([36.74,\infty)\) | .1 |
| \([37.77,\infty)\) | .5 |
| \([39.38,\infty)\) | .9 |
| \([40,\infty)\) | 1 |
| \([40.4,289]\) | 1.05 |
| \([45,80]\) | 1.2 |
| \([45,\infty)\) | \(1+9/L\) |
| \([47.4,56]\) | 1.3 |
| \([47.2,\infty)\) | \(1+14/L\) |
| \([48,180]\) | \(1+14/L+20/L^2\) |
| \([48.3,\infty)\) | \(1+13/L+100/L^2\) |

For the higher-order entries put
\[
 A_j=\sum_{k=0}^j k!\binom{j}{k}-\sum_{k=0}^j k!(j-k)!,\qquad
 P_d(L)=\sum_{j=0}^d A_{j+4}/L^j.
\]
For \(d=2,3,4,7,9,11,13,15,16\), sufficient \(L\)-onsets for \(P_d\) are respectively \(223,263,320,450,620,850,1300,2200,4000\). The first five coefficients are \(1,14,145,1412,13985\). Take the maximum of these branches, the positive sign, the local linear bound and the pointwise analytic bound below. At the earlier onset \(L=45\) one can use the whole-ray margin \(1+9/L\), versus \(1+14/L\) from 47.2. At fixed margin .5 use 37.77 instead of the later 39.38 needed by the .9 row. The \(1+13/L+100/L^2\) profile is better than \(1+14/L\) before their exact crossover \(L=100\), on their overlap. Constant normalized margins \(>1\) are not asserted on whole rays: the same log-integral expansions below with exponential π errors give limiting normalized gap 1.

## Endpoint and finite connection

Platt–Trudgian arXiv:1809.03134v2 Thm. 2, PDF p. 3, prints \(n<x\le e^{58}\) and \(x\ge e^{3915}\). The literal real interpretation at the open left endpoint is false by the obstruction \((n,r]\) proved here. Dudek–Platt arXiv:1407.1901v1 Thm. 1.2, PDF p. 2, gives the older unconditional \(L\ge9658\) sign. Their Thm. 1.3 uses full RH for the ray; we reuse only the published **finite** computation: the start of §3.1, PDF p. 8, reports the largest integer counterexample up to \(10^{11}\); Lemma 3.4, PDF p. 10, gives the sieve/step interval to \(1.15\cdot10^{16}\), not its RH continuation via Lemma 3.2. These are inherited finite trust, not fresh verification. Only the integer conclusions are needed (the printed stepping discussion has endpoint rounding/strictness issues; we do not assert implementation details). On each \([j,j+1)\), \(\pi(x)\) is constant and \(ex\,\pi(x/e)/\log x\) nondecreasing for \(j>e\). The new positive bound from \(L=36.54\) overlaps the computed domain (the code checks even \(e^{36.98}<1.15\cdot10^{16}\)). Thus the real joins use neither the erroneous endpoint nor full RH.

Replaying count.cpp gives \(\pi(m)=b,\pi(n)=\pi(n+1)=c\). Correctness: maintain the count of integers \(2,\ldots,v\) surviving deletion of composites with processed least prime factors. The query set \(1,\ldots,\lfloor\sqrt N\rfloor\) and \(\lfloor N/j\rfloor\) for \(j\le\lfloor\sqrt N\rfloor\) is closed under floor quotient by integers; a repeated boundary representative is harmless. For a newly detected prime \(p\), deletions correspond to \(p\) times the old survivors from \(p\) through \(\lfloor v/p\rfloor\). Traverse decreasing \(v\) so the latter counts have not been modified yet. Before the update the difference at \(p,p-1\) is one iff \(p\) is prime (a composite would have lost its least prime already). Every composite \(\le N\) has a factor \(\le\sqrt N\); all loop integer arithmetic is well within 64 bits on the inputs. The interval arithmetic checks \(m<n/e<(n+1)/e<m+1\), opposite endpoint signs, and the root enclosure. Thus \(R\) really is the scalar function on \([n,n+1]\). Its derivative \(eb(\log x-1)/(\log x)^2\) is positive and decreasing there, and it is certified \(>67000000\) at \(n+1\).

## Bound on the normalized prime-counting error

FiniteRH Cor. 1 (PDF p. 4) supplies the finite \(\theta\) error \(\sqrt{x}\log^2 x/(8\pi)\) for \(599<x\le2.169\cdot10^{25}\); we use the *printed* finite \(\pi\) bound \(\sqrt{x}\log^2 x/(8\pi)\) for \(2657<x\) up to the same cutoff. Both include \(L=58\). FiniteRH §3.3 (PDF p. 5) gives \(\pi(x)<\mathrm{li}(x)\) for \(2\le x\le10^{19}\); use only \(L\le43.74\). Dusart Cor. 4.5 (PDF p. 13) gives \(0\le V(x)=\psi(x)-\theta(x)\le c_U\sqrt{x}+1.78x^{1/3}\), \(c_U=1.000000147\). CH2 Cor. 1.3 (PDF p. 3) gives \(|\psi(x)-x|/x\le b_0+113.67/\sqrt x\), \(b_0=.000000000001048>\pi/H\). On \(34\le L\le58\), use also CH2 Cor. 1.2, with \(T=e^{L/2}/2\) or \(13e^{L/2}/20\), and on \(35\le L\le58\) with \(T=2e^{L/2}/5\). All these heights are at least \(10^7\), below \(H\), and give \(x>\max(T,10^9)\). With \(h_T=\log(T/(2\pi))\), the CH2 bound on \(|\psi-x|/x\) used is
\[
 \pi/(T-1)+\pi^2/(3T^2)+e^{-L/2}\bigl(h_T^2/(2\pi)-h_T/(6\pi)\bigr).
\]
Use \(1\le z\coth z\le1+z^2/3\), from CH2 §7.1 (Eq. 7.2). Add \(V(x)/x\) for a \(\theta\) bound, and take the minimum with the direct finite \(\theta\) bound.

With \(D_\pi(L)=Le^{-L}(\pi(e^L)-\mathrm{li}(e^L))\), \(E_\theta(L)=e^{-L}\theta(e^L)-1\) signed, the exact partial summation from \(a=8\) is
\[
 D_\pi(L)=E_\theta(L)+\frac{L}{a}e^{a-L}(D_\pi(a)-E_\theta(a))
  +Le^{-L}\int_a^L\frac{\theta(e^v)-e^v}{v^2}\,dv .
\]
At \(a=8\) the bracket contributes at most \(Le^{-L}e^4(8^2+8)/(8\pi)\). For the integral use Dusart (2.1) with the oscillatory integration justified in mertens-proof.md. After integrating by parts, a group of zeros with \(\beta\le B\) contributes at most its sum of \(|\gamma|^{-2}\) times
\[
 \frac{e^{BL}}{L^2}\left(1+\frac{2/a}{B-2/a}\right)+\frac{e^{Ba}}{a^2}.
\]
Indeed, retain the boundary terms, then use \(2/v^3\le(2/a)/v^2\) and the log derivative of \(e^{Bv}/v^2\), at least \(B-2/a\). Here \(B=1/2\) up to height \(H\), \(B=7/8\) beyond; use .12 and \(8\cdot10^{-12}\) as in candidate.md. The constant/trivial-zero term contributes at most \(1.84/a\). Subtracting \(V\) adds at most \(4c_U e^{L/2}/L^2+21.36e^{L/3}/L^2\), by the same derivative estimates. This yields fin(L) for \(33\le L\le58\).

For later \(L\), use the same partial summation, with anchor \(a\) at an established error bound. If \(|E_\theta(v)|\le\sum c v^k e^{-gv}\) for \(v\ge a\), \(c,k\ge0,\ 0\le g<1\), an individual mode contributes at most its value at \(L\) times \(L/[a^2(1-g)]\) to the integrated term (bound \(v^k\) and \(v^{-2}\) at favorable endpoints; integrate \(e^{-(1-g)(L-v)}\)). Use CH2 plus Dusart's \(V\) at \(a=58\), then reanchor the same modes at 140. Use \(\mathcal S+V/x\) from \(a=100\) and \(\mathcal F+V/x\) from 140. This gives ch, ch2, sp and rp in the code; the refined rp branch is used on the crossover region only, and is valid beyond it too. Anchors are evaluated at their exact common endpoints. Let \(A(L)\) be the minimum of these error bounds wherever applicable.

## Log-integral model, finite certificates and analytic tail

Use \(N=22\) and \(S_N(L)=\sum_{k<N}k!/L^{k+1}\). At \(L=32\) the arithmetic checks
\[
 S_N(L)<e^{-L}\mathrm{li}(e^L)<S_N(L)+5N!/L^{N+1}.
\]
These strict barriers persist, since \((e^L S_N)'=e^L/L-e^L N!/L^{N+1}\), and adding the correction makes the derivative greater than \(e^L/L\) by \(5(1-(N+1)/32)>1\). The anchor uses \(\mathrm{li}(e^L)=\gamma+\log L+\sum_{k\ge1}L^k/(k\,k!)\) and bounds the positive tail after 200 terms by twice the next term. The identity follows by the PV substitution \(x=e^v\) and expansion of \(e^v\). The constant is \(-\int_0^\infty e^{-t}\log t\,dt=\gamma\): replace \(e^{-t}\) by \((1-t/n)^n\) up to \(n\), zero beyond, and use dominated convergence and the exact logarithmic moment \(n(\log n-H_{n+1})/(n+1)\) by integration by parts with the finite geometric sum.

Put \(u=1/L,\ U(u)=\sum_{k<N}k!u^k+5N!u^N\). The normalized log-integral gap equals
\[
 L^4\{L e^{-(L-1)}\mathrm{li}(e^{L-1})-[L e^{-L}\mathrm{li}(e^L)]^2\}.
\]
For \(L\ge34\), lower bound the first term in braces by the degree-\(2N\) truncation of \(\sum_{k<N}k!u^k/(1-u)^{k+1}\), whose omitted coefficients are positive. Upper bound the square by \(U(u)^2\). Their polynomial difference has coefficients \(C_0,\ldots,C_{2N}\); \(C_0,\ldots,C_3=0\), \(C_j=A_j\) for \(j<N\). For the actual \(\pi\) gap set \(F=0\) when \(L\le43.74\) by the original sign, otherwise \(F=A(L)\). The **pointwise** lower bound on the normalized gap is
\[
 \sum_{j=4}^{2N}C_j L^{4-j}
 -L^4\left(\frac{L}{L-1}A(L-1)+F(2U(1/L)+F)\right).
\]
This combines adverse directions of the two errors; their signs need not coincide. Take its maximum with all other valid profiles. The two-sided barriers and the exponentially decaying π error at infinity also give the claimed limit 1.

ramanujan.py checks the finite part of each simple profile by whole-cell interval enclosures, splitting at joins including 43.74 and using adaptive subdivision where needed. Subtract the target coefficients *before* evaluating the polynomial. A failed interval raises an exception; a printed sample is never evidence for a subinterval. For the analytic tail beyond \(B\), after subtracting the target coefficients, use a positive coefficient at order \(L^{-d}\) and multiply the difference by \(L^d\). Drop nonnegative lower-order terms; bound all negative higher-order terms at \(B\) and discard the positive higher ones. The scaled sp errors decrease from \(B\): the positive mode degrees are at most 3 including the integral prefactor, their decays are at least \(1/8\), and \(B-1>8(8+d)\) handles the shifted argument and the multiplier \(L^{4+d}L/(L-1)\) by the log-derivative test. The extra factors \(U(1/L)\) and sp are decreasing too. At \(B\) evaluate using exact rational upper bounds \(e^{-q}\le (1000/2718)^{\lfloor q\rfloor}\). This handles tiny tails without underflow and proves the comparisons to infinity.

## Tested failures and remaining bottlenecks

A symmetric log-scale \(\pi\) error, from directly integrating the finite \(\theta\) error, left a gap at the upper end of the original finite computation. Optimized verified-height CH2 and integration of the oscillatory error repaired it. The \(1+14/L\) profile initially failed near \(L=189.15\), even with refined zero-density estimates; reanchoring the CH2 estimate at 140 and keeping the nested density bound repaired the entire join. Earlier nearby trial onsets for normalized margins .1, .5 and .9 did not certify; the listed onsets do. Neither the old sign computation nor D01 supplies a quantitative margin on most of the finite interval below the analytic onset. To strengthen that part further would need quantitative information from the finite computation or substantial additional exact prime-count computations. A fixed positive margin immediately at \(r\) is impossible by continuity there. No effect is attributed to D01, and no globally best profile is asserted.

