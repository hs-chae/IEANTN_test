# Ramanujan gap: endpoint, connected ray and quantitative profiles

Assumptions B0, not D01; see common.md. Set \(L=\log x\) and \(Y(L)=L^6R(e^L)/e^{2L}\). All logs and rays here denote **real** arguments. Strict lower bounds:

| Log-domain (closed) | \(Y(L)>\) |
|---|---:|
| [36.98,37.5] | .10 |
| [37.5,39.32] | .32 |
| [39.1,39.32] | .8 |
| [39.32,39.5] | .065 |
| [39.5,40] | .145 |
| [40,42.8] | .35 |
| [42.8,∞) | 1 |
| [43,60] | 1.038 |
| [46,77] | 1.209 |
| [47,67] | 1.246 |

In particular .065 at onset 36.98, .145 at onset 39.5, .35 at onset 40 and unit margin at onset 42.8 are **whole rays**. Retain the greatest applicable certified branch and the explicit continuous-variable lower profile below. The interval tradeoffs with margin greater than one are not assertions of eventual uniform margins greater than one.

**Exact real last failure at the published-computation trust tier.** Let \(N=38358837682\), \(A=1644673232\), \(B=632207037\). Let \(z\) be the unique solution in \((N,N+1)\) to \(ezB/\log z=A^2\). The certified bracket is
\[
 38358837682.21792636514419 < z < 38358837682.21792636514511.
\]
Then \(R(x)>0\) for all real \(x>z\), \(R(z)=0\), and \(R(x)<0\) on \([N,z)\). The least integer strict-ray onset is \(N+1\); the strict real ray is open. On \([z,N+1]\) one also has \(R(x)\ge 67000000(x-z)\).

The connected finite bridge is now checked partly from fresh exact computation. First, \([N+1,10^{11}]\) follows from bridge.py and bridge.c (details below), with \(R(N+1)>0\) checked by the local formula. Next use DudekPlatt2015 Lemma 3.4 (PDF p.10) on \([10^{11},1.15\cdot10^{16}]\), its finite computation free of full RH. Even just its integer restriction would suffice up to \(\lfloor 1.15\cdot 10^{16}\rfloor\) inclusive, since on a unit interval \([n,n+1)\), \(\pi(x)=\pi(n)\), while \(\pi(x/e)\) and \(ex/\log x\) are nondecreasing for \(x>e\). Finally \(e^{36.98}<1.15\cdot10^{16}\), and the analytic margins apply starting at \(e^{36.98}\). The printed lower boundary of PlattTrudgian2021 Theorem 2, PDF p.3, is not used as a real onset: it is false interpreted as \(R(x)>0\) for all real \(x>N\). The computed interval \([N,N+1)\) uses \(\lfloor x/e\rfloor=14111427770\) (certified at both ends), and \(\pi(N)=A\), \(\pi(14111427770)=B\) from count.py, so the root is exact. The sign tests are directed and strict, and \(e B(\log x-1)/(\log x)^2>67000000\) throughout that unit interval. At \(N+1\) the formula still holds, since \(N+1=2521\cdot15215723\) is composite and the same denominator-cutoff floor is certified there.

**Counting algorithm.** With \(n\) the query, \(V\) consists of distinct \(\lfloor n/i\rfloor\), including every integer through \(\lfloor\sqrt n\rfloor\); the code generates these in descending order. Before striking a prime \(p\), \(S(v)\) counts integers in \([2,v]\) not divisible by a smaller prime, *plus* the smaller primes themselves. For composite \(p\le\sqrt n\), \(S(p)=S(p-1)\) so skip it. Removed multiples of a prime \(p\) are \(p b\) with \(p\le b\le v/p\) and no prime factor below \(p\); their count is \(S(\lfloor v/p\rfloor)-S(p-1)\). Closure uses \(\lfloor\lfloor n/i\rfloor/p\rfloor=\lfloor n/(ip)\rfloor\); descending order keeps the old values for the updates. All composites in \([2,n]\) have a prime factor at most \(\sqrt n\), proving the query result. No numerical paper table is used for the local counts.

**Independent near-endpoint sieve join.** bridge.py uses the same C runtime via GCC and supplies the upper integer \(g_n=\lceil S\log n\rceil\) (or its directed upper enclosure) for each block start \(n=N+1+10^6 j\), truncated at \(10^{11}\). Scale \(S=10^{16}\). The bounds \(e_l/S<e<e_u/S\) with \(e_l=27182818284590452\), \(e_u=e_l+1\) are checked. The exact lower denominator query \(\lfloor Sp/e_u\rfloor\le\lfloor p/e\rfloor\) is used at each prime \(p\) in the block. The log upper bound uses \(\log p\le \log n+(p-n)/n\). Endpoints and integer counts are checked strictly using
\[
 e_l\,p\,\pi(\lfloor Sp/e_u\rfloor)>
    [g_n+\lceil S/n\rceil(p-n)]\,\pi(p)^2 .
\]
Counts start at the two independently checked local values (there is no prime at the left endpoint \(N+1\)). The segmented sieve marks odd multiples starting no earlier than the square of the corresponding base prime. Every odd composite through \(10^{11}\) has a prime divisor at most 316227; the other stream never exceeds \(10^{11}\). Both running streams count each prime in their successive nonoverlapping blocks exactly once. The log test is outward and uses unsigned 128-bit products, with counts checked below \(10^{10}\), log bound below \(3.01\cdot10^{17}\), and both sides fitting \(2^{128}\). Only prime jumps of \(\pi(x)\) can cause a downward jump of \(R\); between them \(\pi(x/e)\) and \(ex/\log x\) are nondecreasing. The run checked exactly 2,473,381,581 prime jumps and ended at counts 4,118,054,813 and 1,580,158,781 at \(10^{11}\) and 36,787,944,117. This is an ordinary replayable C computation, not formally verified execution.

## Explicit pi approximations

Use \(\operatorname{Li}_2(x)=\int_2^x dy/\log y\); this is not the PV li. Put \(S_m(L)=\sum_{j=0}^m j!/L^j\) and \(F_m(x)=x S_m(\log x)/\log x\). Partial summation gives exactly
\[
 \frac Lx(\pi(x)-\operatorname{Li}_2(x))=
 u_\theta(L)+L e^{-L}\Big(\frac2{\log2}+
                 \int_{\log2}^{L}\frac{e^t u_\theta(t)}{t^2}\,dt\Big),
 \quad u_\theta(t)=e^{-t}\theta(e^t)-1 .
\]
The following are envelopes for the absolute error (except the explicitly one-sided improvement). They are the functions EC, EF, EF2 and ED in verify.py. Bound an initial integral through \(b=7\) or \(12\), including the \(2/\log2\) term, by \(3e^b\), using \(|u_\theta|\le1\) (Dusart Thm 4.2, PDF p.11); indeed \(2/\log2+e^b/(\log2)^2<3e^b\).

1. **EC (L≥12).** CH2 Cor. 1.3 (PDF p.3) gives \(c+113.67e^{-L/2}\) for \(u\), where \(c=1.048\cdot10^{-12}>\pi/H\). Dusart Cor.4.5 (PDF p.13) bounds \(\psi-\theta\) by \(1.000000147\sqrt x+1.78 x^{1/3}\). Thus \(|u_\theta|\le c+117 e^{-L/2}\). Integrate \(e^t/t^2\) and \(e^{t/2}/t^2\) using their logarithmic derivatives \(\ge5/6\) and \(\ge1/3\) for \(t\ge12\), respectively. This gives
\[
 E_C(L)=3Le^{12-L}+c(1+1.2/L)+117e^{-L/2}(1+3/L).
\]
2. **EF ([7,58]).** PlattTrudgian2021 Lemma 6 (PDF p.9–10), also within the theta range in PlattTrudgianFiniteRH Cor. 1 (PDF p.4), bounds \(|u_\theta|\le L^2 e^{-L/2}/(8\pi)\). The integral gives \(E_F(L)=3Le^{7-L}+(L^2+2L)e^{-L/2}/(8\pi)\).
3. **EF2 ([34,58]).** CH2 Cor. 9.3 (PDF p.36), with \(T=2\pi^2 e^{L/2}/L\) between \(10^7\) and H, gives \(( (L-w)^2-4)e^{-L/2}/(8\pi)\) for \(|u|\), where \(w=2\log(L/(\pi e))\). The difference from \((L-2.4)^2 e^{-L/2}/(8\pi)\) is at least \(1.007e^{-L/2}\): at 34 check \((w-2.4)(2L-w-2.4)+4>8\pi\cdot1.007\); both factors are nonnegative and increasing thereafter. Dusart Cor. 4.5 costs \(<1.007e^{-L/2}\) on this band. Split the integral for EF at 34, using \(k=(1-2.4/L)^2\) as a bound on \((1-2.4/t)^2\) for \(34\le t\le L\):
\[
 E_{F2}(L)=3Le^{7-L}+\frac{e^{-L/2}}{8\pi}
       [(L-2.4)^2+2L(k+(1-k)e^{(34-L)/2})].
\]
For the upper error only, subtract \(2 e^{-L/2}[1+(2/L)(1-e^{(34-L)/2})]\) from this envelope. Indeed \(\psi-\theta\ge .9999\sqrt x\) (Dusart Prop. 4.3, PDF p.12), while the psi bound above already had spare \(1.007e^{-L/2}\). There is thus a gain of \(2 e^{-t/2}\) in the upper local theta bound; use \(\int_{34}^L e^{t/2}/t^2\,dt\ge2(e^{L/2}-e^{17})/L^2\). The reduced EF2 remains positive (its local term alone before subtraction exceeds \(2e^{-L/2}\), and its integral comparison is nonnegative).
4. **ED (L≥100).** Use the density list \(\mathcal D\) and add \((.5,3,0)\) to bound \(|u_\theta|\). Keep the *integral prefix* through 100 from EC, not the local theta error there. Its bound in units of \(e^{100}\) is \(3e^{12-100}+(1.2c+351e^{-50})/100^2<2\cdot10^{-16}\). For each triple after 100 the logarithmic derivative of \(e^{(1-r)t}t^{k-2}\) is at least \(.98-r>0\). Therefore the ED bound is
\[
 E_D(L)=2\cdot10^{-16}L e^{100-L}
       +\sum_{(r,a,k)} aL^k e^{-rL}[1+1/((.98-r)L)].
\]

**Truncation.** \(F_m'(x)=1/\log x-(m+1)!/(\log x)^{m+2}\). For \(m=18\), at \(b=30\) the anchor \(\operatorname{Li}_2(e^b)-F_{18}(e^b)\) lies strictly between 12 and 13. The program computes it by integrating the positive exponential series from \(\log2\) to b with a geometric upper remainder starting at index 160 (ratio below 1/2). For \(L\ge30\), the logarithmic derivative of \(e^t/t^{20}\) is at least 1/3. Thus \(\operatorname{Li}_2-F_{18}>0\), and its normalized upper error is \(13Le^{-L}+3\cdot19!/L^{19}\).

Define \(U(L)\) and \(V(L)\) as upper and lower normalized errors from \(S_{18}\) for \(L\pi(e^L)/e^L\): take the minima of applicable EC, EF, EF2 and ED with their appropriate sidedness; add the last truncation upper error to \(U\), and nothing to \(V\). For \(36.98\le L\) and \(e^L\le1.2\cdot10^{17}\), further reduce \(U\) using DudekPlatt2015 proof of Lemma 3.2 (PDF p.8), which records the computed fact \(\pi(x)<\operatorname{li}(x)\) up to \(1.2\cdot10^{17}\). Use \(\operatorname{li}(x)=\operatorname{Li}_2(x)+\operatorname{li}(2)\), with \(\operatorname{li}(2)<3\). For instance the PV normalization gives \(\gamma+\log\log 2+\sum_{j\ge1}(\log2)^j/(j\,j!)<3\), by integrating the exponential series and evaluating the usual Euler-constant normalization; alternatively directly bound the PV as written below. The finite published verification invoked there for this sign fact is inherited, not an assertion of full RH.

A direct bound for \(\operatorname{li}(2)\) avoiding the Euler-constant normalization: writing PV as \(\mathrm{PV}\int_{-\infty}^{\log 2}e^t/t\,dt\), discard the negative contribution below \(-1\). On \([-1,\log 2]\), subtraction of \(1/t\) leaves \(\log\log 2\) plus an integral bounded by \(1+2\log 2<3\), using \((e^t-1)/t=\int_0^1 e^{ut}\,du\). The PV is unchanged by this variable substitution (ratios of deleted left and right cutoff lengths tend to 1).

## Profile and certification

For \(L\ge36.98\), set \(S=S_{18}\), \(G(L)=L^4[(L/(L-1)) S(L-1)-S(L)^2]\). A pointwise lower profile for \(Y(L)\) is
\[
 G(L)-L^4\left[\frac L{L-1}V(L-1)+2S(L)U(L)+U(L)^2\right] .
\]
The estimate follows by lower-bounding \(\pi(x/e)\) and upper-bounding the square; the positive factors are as displayed. To reproduce the certified finite margins, use verify.py. It uses \(G\) at each right endpoint and interval bounds on the nonnegative loss over the **whole closed cell**; at boundaries with switching formulas it uses only branches valid on the entire cell. In the one-sided rows it uses the PV improvement on the whole cell. All grid endpoints are finite decimals. There is no use of point samples for the cell errors.

For \(L>1\), \(G\) has the absolutely convergent expansion \(\sum_{j\ge4} C_j L^{4-j}\), with the coefficients
\[
 C_j=\sum_{i=0}^{\min(j,18)} i!\binom ji
       -\sum_{\max(0,j-18)\le i\le\min(j,18)} i!(j-i)!.
\]
The square sum is zero for \(j>36\). The first four coefficients vanish and \(C_4,\ldots,C_{27}>0\). The finite exact inequality \(\sum_{j=28}^{36}(j-4)\max(-C_j,0)/36^{j-27}<23 C_{27}\) absorbs all negative derivatives in \(-G'\) for \(L\ge36.98\), and also absorbs the corresponding negative values in \(G\) itself. Consequently \(G\) is decreasing throughout that range and \(G>\sum_{j=4}^{n+1}C_j L^{4-j}\) for \(4\le n\le17\).

For \(4\le n\le17\) write \(P_n(L)=\sum_{j=4}^n C_j L^{4-j}\); it begins \(1+14/L+145/L^2+1412/L^3+13985/L^4+\cdots\). The tail certificate uses
\[
 E_-(L)=E_D(L-1)+13(L-1)e^{1-L}+3\cdot19!/(L-1)^{19}.
\]
It bounds both approximation errors for \(L\ge101\). At the certified onset \(a\), it checks \(L/(L-1)+2 S(L)+E_-(L)<3.1\) and \(3.1 L^{n+1}E_-(L)<C_{n+1}\); these continue to hold by termwise decrease. For each term \((L-1)^k e^{-r(L-1)} L^{n+1}\) the log derivative is \(\le(n+1+k)/(L-1)-r\); the verification takes \(a-1>8(n+3)\). The inverse-power remainder is decreasing after scaling since \(19>n+1\). This proves \(Y>P_n\) on the full ray. The degree-4 tail from 163 closes the finite check [60,163]. Further certified pairs (degree, log-onset) are (5,191), (6,223), (8,290), (10,360), (12,432), (14,504), (16,577), (17,620).

Higher orders are not limited by the degree-18 proof. For any integer \(n\ge4\), general.py uses \(m=n+2,\ b=2(m+2)\), the same formula for coefficients with 18 replaced by \(m\), and certifies a real ray \(Y>P_n\). All coefficients through \(j=m\) are those of the full factorial expansion; for \(4\le j\le m\) they are positive, since after division by \(j!\) the first sum is \(\sum_{i=0}^j1/i!>8/3\), while the second is at most \(2+2/j+2(j-3)/(j(j-1))\le8/3\). At b, \(\operatorname{Li}_2(e^b)\le e^b/\log2\) and \(F_m(e^b)\le2e^b/b\). The normalized absolute truncation error for \(L\ge b\) is at most \(3Le^{b-L}+2(m+1)!/L^{m+1}\), using logarithmic derivative \(\ge1/2\) in the remainder. The program checks the finite negative tail of \(G_m\) from \(j=m+1\) to \(2m\) is absorbed by \(C_m/L^{m-4}\) at a, hence later. It then uses the same \(3.1\)-loss test and monotonicity. Every test eventually holds, since \(m+1>n+1\), the negative polynomial tail after scaling by \(L^{m-4}\) tends to zero, and the other losses decay exponentially. This gives executable thresholds at arbitrary fixed higher order, not a convergent infinite asymptotic series. Examples replayed: (20,722), (24,868), (32,1161), (48,1748), (64,2336).

## Comparison and limitations

The inherited sign results are PlattTrudgian2021 Thm 2 (integer restriction of its finite segment as a comparison branch, real high ray \(L\ge3915\)) and DudekPlatt2015 Thm 1.2 (PDF p.2, \(L\ge9658\)); their conditional full-RH claim is not an input here. The new absolute-constant density bound and factorial profiles join the missing real band and strengthen sign to positive margins on the stated matched domains. The local root and the near-endpoint sieve do not reverify the much longer inherited Dudek–Platt finite sieve above \(10^{11}\). B0+D01 ties the whole B0 envelope exactly by common.md. For example D01 alone brings a much larger PNT error at \(L=200\), so substituting it in the tail comparison cannot produce an improvement. The CH2 floor alone eventually loses all quantitative margins because \(L^4 c\) grows. Early analytic margin is limited by local theta / prime-counting errors (especially across the end of the inherited \(\pi<\mathrm{li}\) range), not by a large-x power assumption. We used signed prime-power subtraction, a same-normalization Li bound, competing partial-summation branches and analytic high-order tails to improve these bottlenecks. Enlarging the finite one-sided sign computation would require new very-large-scale prime data. The degree-5 two-sided version of the same estimate also yields \(Y=1+14/L+O(L^{-2})\) using the same factorial expansion and absolute exponential error, so a fixed whole-ray margin \(>1\) is impossible.

The new proof in **gap_repair.md** extends the analytic profile back to (L=36.54), improves the connected fixed margins and several finite bands, and moves the higher-order onsets. The exact last-failure and near-endpoint assertions here are unchanged. Take the greatest applicable branch.
