# Mertens products and related prime sums

All assumptions are B0 (candidate.md); every inequality is for real \(x>1\) in its stated domain, with right-continuous prime counting. Define \(P=\prod_{p\le x}(1-1/p)\), \(Q=1/P\), \(W_1=\sum_{p\le x}1/p,\ W_2=\sum_{p\le x}\log p/p,\ L=\log x\). The four errors in order are
\[
 |e^\gamma LP-1|,\quad |e^{-\gamma}Q/L-1|,\quad
 |W_1-\log L-M|,\quad |W_2-L+B_3|.
\]
The original constants in Dusart Theorems 5.6 and 5.7 are \(M=\gamma+\sum_p(\log(1-1/p)+1/p)\), \(B_3=\gamma+\sum_p\log p/[p(p-1)]\), in particular \(W_2\) is normalized by \(L-B_3\), not \(L-\gamma\).

## Explicit rays and comparison

All onsets are included. New numerical certificates are strict on their own pieces; where a join relies on an original weak inequality the complete joined ray is weak.

| \(L\) from | First three errors bounded by | Fourth error bounded by |
|---:|---:|---:|
| 16 | \(.185/L^3\) | \(.175/L^2\) |
| 17.83 | \(.09/L^3\) | \(.09/L^2\) |
| 22 | \(.5/L^4\) | \(.5/L^3\) |
| 34 | \(4/L^5\) | \(4/L^4\) |
| 56 | \(.3/L^6\) | \(.3/L^5\) |

Power rays have bounds \(C x^{-1/8}/L\) (first three) and \(C x^{-1/8}\) (fourth), with exact \((L,C)\) pairs
\[
 (13,.0215),(200,.0196),(225,.018),(250,.017),(300,.016),(350,.015),
 (420,.014),(600,.013),(1000,.0119),(2000,.0114),(5000,.011).
\]
These four outputs are correlated consequences. Retain all applicable branches pointwise; no simultaneous best coefficient and earliest onset is assumed. The log-power rows successively dominate on their overlaps by direct division. For power rays vs \(A/L^k\), the ratio \((C/A)L^{k-r}e^{-L/8}\), \(r=1\) for the first three and \(r=0\) for the fourth, decreases after \(8(k-r)\). In particular the \(L=200\) power row beats the \(L=56\) polynomial row throughout their overlap (ratio \(<.3\) at 200). The earlier \(L=13\) power ray is not substituted for a smaller bound on overlapping intermediate domains.

Keep Dusart Theorems 5.6–5.9 (PDF pp. 17–20): \(.2/L^3\) for products from \(2278382\), and for \(W_1\) from \(2278383\), and \(.3/L^2\) for \(W_2\) from \(912560\). In fact the **same margins** hold from **2278381.72** (both products), **2278382.13** (\(W_1\)), and **912559.998** (\(W_2\)) by clipped-cell certificates joined to the original rays. These improve real onsets, not the sufficient integer onsets. The corresponding violations at **2278381.70** (\(Q\)), **2278382.1** (\(W_1\)), and **912559.996** (\(W_2\)) give certified local obstructions at those coefficients. At fixed onset \(e^{16}\), .185 respectively .175 are better than the original .2 respectively .3; .09 is a later stronger coefficient. Earlier real onsets with weaker coefficients (finite joins to the original rays):

| \(C\) in \(C/L^3\) | Common \(x\)-onset for first three |
|---:|---:|
| .202 | 2278343 |
| .21 | 1526807 |
| .225 | 1525471 |
| .25 | 1514831 |
| .275 | 912581 |
| .3 | 624917 |

| \(C\) in \(C/L^2\) | \(x\)-onset for fourth |
|---:|---:|
| .301 | 912559 |
| .31 | 910277 |
| .33 | 624917 |
| .36 | 618083 |
| .4 | 368359 |

## Pointwise envelope: signed transforms

Set \(E(v)=e^{-v}\psi(e^v)-1\) and
\[
 D(v)=\sum_{n\le e^v}\Lambda(n)/n-v+\gamma,\qquad
 Z(v)=\sum_{2\le n\le e^v}\Lambda(n)/(n\log n)-\log v-\gamma .
\]
Partial summation gives
\[
 D(L)=E(L)-\int_L^\infty E(v)\,dv,\qquad
 Z(L)=E(L)/L-\int_L^\infty E(v)(1/v+1/v^2)\,dv
      =D(L)/L-\int_L^\infty D(v)/v^2\,dv .
\]
For the constants at infinity, use Dusart's asymptotics for \(W_2\) and \(Q\), with the convergent power sum defining \(B_3\) and the convergent unweighted higher-power sum (hence all its tails tend to zero). The \(E\) integrals converge by candidate.md. The error boundary terms use raw values, not mid-jump values.

Let \(B(x)=\sum_{p^j>x,j\ge2}\log p/p^j,\ A_*(x)=\sum_{p^j>x,j\ge2}1/(jp^j),\ C_*(x)=\sum_{p>x,j\ge2}1/(jp^j)\). The signed errors for \(W_2,W_1,\log(e^{-\gamma}Q/L)\) are respectively \(D+B,\ Z+A_*,\ Z+A_*-C_*\). For \(C_*\), summing \(1/[2p(p-1)]\) over integers gives \(0\le C_*\le1/(2\lfloor x\rfloor)\le1/(2(x-1))\).

For \(L\ge13\) write \(r=e^{-L/2},s=e^{-2L/3},c_U=1.000000147\). Choose \(K\) bounding \(|\theta(e^v)-e^v|/e^v\) for every \(v\ge L/2\). Use the minimum of CH2 Cor. 1.3 plus Dusart Cor. 4.5 evaluated at \(L/2\) (decreasing), the finite-RH \(\theta\) bound at \(L/2\) if \(L/2\le58\) together with the maximum with the CH2-plus-Dusart bound at 58, and applicable decreasing Dusart Thm. 4.2 rows at \(e^{L/2}\), in particular \(1.2323/(L/2)\). The finite-RH \(\theta\) domain applies because \(e^{6.5}>599\), and its bound decreases on the required range. Using
\[
 (1-K)\sqrt{t}\le\theta(\sqrt{t})\le V(t)\le c_U\sqrt{t}+1.78t^{1/3}\quad(t\ge x)
\]
and \(B=-V(x)/x+\int_x^\infty V(t)dt/t^2\), one obtains
\[
 b_-=\max(0,(2(1-K)-c_U)r-1.78s)\le B\le b_+=(2c_U-1+K)r+2.67s.
\]
Use the same \(K\) in \(b_+\) for every argument larger than \(x\). Then \(A_*=B/L-\int_L^\infty B(e^v)dv/v^2\) gives
\[
 a_-=\max(0,b_-/L-[2(2c_U-1+K)r+4.005s]/L^2)\le A_*\le a_+=b_+/L.
\]

### Oscillatory integration (also used for Ramanujan)

Use Dusart (2.1), PDF pp. 3–4, by symmetric heights, with the original mid-value convention at jumps, irrelevant for integration. It gives
\[
 E(v)=-\sum_\rho e^{(\rho-1)v}/\rho+e^{-v}g(v),\qquad
 g(v)=-\log(2\pi)-\tfrac12\log(1-e^{-2v}),\quad |g(v)|<1.84\ (v\ge\log2).
\]
To justify termwise integration, choose a nonnegative smooth compactly supported weight at least 1 on any given compact interval. In the weighted squared norm of a zero-sum tail, two integrations by parts bound the kernel with phase \((\gamma-\gamma')v\) by \(C/(1+(\gamma-\gamma')^2)\), uniformly in the two real parts. FKS Lemma 2.1 and the count difference over a slightly enlarged unit bin imply \(O(\log(2+|j|))\) zeros in bin \(j\), so their sum of \(1/|\rho|\) is \(O(\log(2+|j|)/(1+|j|))\). This is a square-summable sequence. The kernel on bins is bounded by a summable multiple of \(1/(1+(j-k)^2)\); use \(a_j a_k\le(a_j^2+a_k^2)/2\) for the double sum. Thus the tail squared norms tend to zero. The local \(L^2\) limit agrees almost everywhere with the formula by the pointwise limit and a subsequence. Integration against bounded weights on compact intervals follows, also for unnormalized \(\psi(e^v)-e^v\) by multiplying by \(e^v\).

For the weight \(f(v)=1/v+1/v^2\), use \(f(L+y)=\int_0^\infty(1+t)e^{-(L+y)t}dt\). For a single zero, integrate first in \(y\ge0\); absolute convergence for that zero follows from \(\beta<1\), and \(|1+t-\rho|\ge|\gamma|\), \(|\rho|\ge|\gamma|\). This bounds its integral by \(f(L)e^{(\beta-1)L}/\gamma^2\); for \(f=1\) use direct integration. All integrated contributions sum absolutely by candidate.md. The upper-end tails at \(V\to\infty\) vanish in absolute sum by the bound \(f(V)e^{-V/8}\sum|\gamma|^{-2}\). The constant/trivial term integrates to at most \(1.84e^{-L}\) or \(1.84e^{-L}/L\), the latter using the exact primitive. Thus with \(J=.12r+8\cdot10^{-12}e^{-L/8}\) and \(-p_-\le E(L)\le p_+\) one can take signed intervals \([-d_-,d_+]\) for \(D\) and \([-z_-,z_+]\) for \(Z\), where
\[
 d_\pm=p_\pm+J+1.84e^{-L},\qquad
 z_\pm=[p_\pm+(1+1/L)J+1.84e^{-L}]/L.
\]
Then make the following pointwise improvements.

* For \(p_\pm\) take the smallest applicable bounds, including CH2 Cor. 1.3 (PDF p. 3); CH2 Lemma 9.2 (.791 and .751 times \(r\) on \(13\le L\le29.9\), PDF p. 35); FiniteRH Cor. 1 through \(L=58\); CH2 Cor. 1.2 with \(T=10^7\) from \(L=30\), \(T=e^{L/2}/2\) and \(13e^{L/2}/20\) from \(L=34\), \(T=2e^{L/2}/5\) from \(L=35\) (all through 58 in the implementation, using the expression in ramanujan-proof.md), and \(\min(\mathcal S,\mathcal F)\) from 100. As extra parameterized branches one can take every valid CH2 \(T\) and the \(\psi\) bounds of Dusart Prop. 3.2/Table 1 and Thm. 3.3, FKS Thms. 1.1–1.2/Tables 5–6 and Cor. 1.4, and Platt–Trudgian Thm. 1/Table 1, on their own domains. None is strengthened by plugging in D01.
* Intersect the \(D\) interval with the CH2 weighted-\(\psi\) bound \(w=b_0+113.67r\), or the optional reported normalized CH2 finite-computation bound (see repair.md, not the literal Lemma 9.2 display) \(.8r\) for \(13\le L\le27.6\). For \(Z\), the \(D\)-identity gives another bound \(|D(L)|/L+\int_L^\infty|D(v)|dv/v^2\). Bound the integral by \(b_0/L+2(113.67)r/L^2\); for \(L\le27\) also split at 27 and use \(.8\) before it, giving \(1.6r/L^2+b_0/27+2(113.67)e^{-27/2}/27^2\). The normalized option is now opt-in via `normalized=True`; these are jw and wcap in mertens.py. The repaired main polynomial portfolio does not need this option. A fixed admissible CH2 Cor. 1.2 height also gives a weighted-\(\psi\) envelope at every larger argument and can be used in this integral.

For the log normalized \(Q\) take the signed interval \([\ell,u]=[-z_-+\max(0,a_--1/(2(x-1))),\, z_++a_+]\); the relative \(P,Q\) errors are respectively bounded by \(\max(1-e^{-u},e^{-\ell}-1)\) and \(\max(e^u-1,1-e^\ell)\). For \(W_1\) use \([-z_-+a_-,z_++a_+]\); for \(W_2\) use \([-d_-+b_-,d_++b_+]\). Signed bias and the reciprocal relationship are accounted for before taking radii.

Keep all applicable original branches too. In addition to the four stated ray estimates, use direct \(\theta\) transfers: for signed normalized \(\theta\) error use its boundary value divided by \(L\) (respectively undivided), minus its tail integral with kernel \((1/v+1/v^2)\) (respectively 1), for \(W_1\) (respectively \(W_2\)); these are the identities in Dusart Thms. 5.6–5.7. In the subtracted integral the upper and lower input bounds exchange roles. In particular a single Dusart Thm. 4.2 row \((\eta,k,x_k)\) gives on \(x\ge x_k\)
\[
 \eta/(k L^k)+\eta(1+1/(k+1))/L^{k+1}\ (k>0),\qquad
 \eta/((k-1)L^{k-1})+\eta/L^k\ (k>1).
\]
These include fallback branches for all \(x\ge2\). Retain FiniteRH Cor. 1 and §3.3 (finite \(\theta<x\)), Platt–Trudgian Cor. 1/Table 1, and \(\psi\)-to-\(\theta\) consequences of the valid \(\psi\) inputs by \(0\le V\le c_U\sqrt{x}+1.78x^{1/3}\). Take the pointwise envelope of applicable inputs before integration if desired, splitting at domain boundaries. For the products subtract \(C_*\) from the \(W_1\) signed interval as above, then exponentiate. For \(1<x<2\) the four raw quantities are known exactly. The complete portfolio is the intersection/minimum over applicable branches including the finite bounds, not a single chosen asymptotic branch. Redundancy compares against **any** lawful original envelope, so does not require an exhaustive enumeration of all consequences of the originals.

## Certificates on the rays and at finite joins

For the power rays with \(L\ge B\ge200\), mertens.py evaluates the expression U (variable a in tail), a positive majorant of \(e^{L/8}\) times the \(W_2\) error and \(Le^{L/8}\) times the log product or \(W_1\) error. It comprises \(e^{L/8}\mathcal F(L)\) and the displayed corrections for \(J,g,b_+\); use \(K<.001\) by Dusart Thm. 4.2 at \(e^{L/2}\), giving \(b_+\le1.002r+2.67s\). Every term of U decreases or is constant from 200 (for positive polynomial powers the rates are \(3/40\) or \(3/8\)). For the products use \(e^t-1\le t/(1-t)\) for \(0\le t<1\); the check \(U(B)/(1-U(B)e^{-B/8}/B)<C\) proves the entire ray. The \(L=13\) power row is checked on an interval cover through 200 then joins to the stronger row. The polynomial rows are checked by outward interval covers through 240, with source joins honored, then the power bound with .021 beats the requested polynomial by the derivative test above. Each interval leaf is checked, including between any displayed sample points.

mertens.py scan sieves to \(N_c=10^7\) and checks the finite error cells through 2278383. Eratosthenes marks exactly the composites (start at \(p^2\) at each unmarked \(p\)). It accumulates \(\log Q,W_1,W_2\) and the truncated constants. For \(t\ge N_c\), \(|\theta(t)-t|/t<.0007\): use CH2 Lemma 9.2 plus Dusart 4.5 to \(e^{29.9}\), then FiniteRH Cor. 1 to \(e^{58}\), then CH2 Cor. 1.3 plus Dusart 4.5. Each piece decreases; left endpoints checked. Write \(N=N_c,\ K=.0007\) for this calculation. For a positive decreasing weight \(w\) with \(tw(t)\to0\), the tail \(\int_{(N,\infty)}w\,d\theta\) differs from \(I_0=\int_N^\infty w\,dt\) by at most \(K(2Nw(N)+I_0)\) by partial integration. For \(B_3\), \(w=1/(t(t-1)), I_0=-\log(1-1/N)\). For the constant subtracted from \(\gamma\) to give \(M\), use \(w=1/(2t^2\log t)\) and a positive residual at most \(1/[3(N-1)^2]\) from the \(j\ge3\) terms, summing \(1/[3(p-1)^3]\) over integers. For \(I_0\), the first five and six terms \((-1)^j j!/(2N\log^{j+1}N)\) give upper and lower by repeated parts and the sign of the final integral. The tail error is at most \(3K/(2N\log N)\). No published decimal approximations for \(M,B_3\) are used.

On each prime cell \([p,q)\) the raw quantities are constant. The check evaluates the value at \(p\) and the left limit at \(q\); the next cell checks the right value at \(q\). For the signed normalized \(P,Q\) errors times \(L^3\), derivatives are \(L^2(4e^\gamma LP-3)>0\) and \(L^2(2e^{-\gamma}Q/L-3)<0\) under the checked guards (first product \(>.75\) at \(p\), second \(<1.5\) there; they respectively increase and decrease). For \(W_1\) times \(L^3\), derivative is \(L^2(3(W_1-\log L-M)-1)<0\) if the left unscaled signed error is \(<1/3\); for \(W_2\) times \(L^2\), it is \(L(2(W_2-L+B_3)-L)<0\) if the left signed error is \(<L/2\). The per-cell guards suffice everywhere on those cells since the unscaled sum errors decrease. This proves each whole-cell or clipped-cell inequality from its endpoint enclosures. Reporting the end of the last not-certified cell before the original onset gives the weaker-coefficient rows. For the same margins the final cells are clipped at exact rational starts, with exact signed lower enclosures also giving the recorded violations. The code's integrality does not restrict the resulting domain to integers.

## Improvements and bottlenecks

Direct D01 with only absolute integration would give \(D\) at most \((1/64)e^{-L/8}(9L^2+128L+1024)\) and \(Z\) at most \((1/64)e^{-L/8}(9L+72)\) in absolute value before the corrections. B0 alone gives the stronger forms here with two fewer log powers, reduced coefficients, and earlier valid branches. The crude initial constant tails from summing over integers obscured the near-threshold signs. Weighted \(\theta\) tails, the larger constant sieve, and clipped-cell comparisons expose provable same-margin improvements, with explicit nearby barriers. The obstruction to an even better asymptotic power in this method is non-exclusion of zeros at or arbitrarily close to \(\beta=7/8\); D01 does not exclude those. Smaller eventual coefficients would be plausible with sharper reciprocal density or cancellation, not established here. No optimality claim, no reliance on floating samples, and no D01 effect.

