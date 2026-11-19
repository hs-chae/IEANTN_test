# Ramanujan gap: finite joins, higher profiles, and corrected inherited scope

For real \(x>1\), inclusive prime counts, write \(L=\log x\),
\(R=ex\pi(x/e)/L-\pi(x)^2\) and \(Y=L^6R/x^2\).
All inequalities for Y in the tables are strict; all displayed finite and one-sided log endpoints are included. Positive margins in units Y correspond to multiplying by \(x^2/L^6\).

## Connected profiles

Using B0+D02 the following quadratic profiles hold on the entire indicated real rays:
\[
 Y> 1+14/L+z/L^2.
\]

| log onset | z | log onset | z |
|---:|---:|---:|---:|
|47.647|8.39|48.27|40|
|47.677|10|48.49|50|
|47.955|25|49|70|
|48|27|49.30|80|
|49.31|80.6|171.85|100|
|172|100|176|119|
|180|133| | |

Apply also \(z=120\) on \([176,187]\) (not promoted to a ray from this check), and keep all old finite branches. The rows through 49.31 use closed whole cells to 172 and the verified tail at 172 (the separately checked \(z=93\) tail suffices for these joins). The entire \(+100\) ray starting at 171.85 is disjoint from the earlier [50,158] finite slab that already had \(+100\) but there is **not** a \(+100\) connection across the new near-169 transition. The supported \(+80.6\) is a genuine connected improvement rather than a splice that omits the plateau transition. The fixed .04/.30/.70/1 comparisons and additional early B0 results are below.

Finite B0+D02 comparisons also give the full quadratic \(+145/L^2\) on \([52.99,123]\) (overlapping checks), full quadratic plus \(1050/L^3\) on \([56,106]\), plus \(1060/L^3\) on \([56,105]\). The far full quadratic begins at L=187 (D01: L=221). At fixed onset L=48 the connected certified coefficient is at least 27, versus 8.34 in the D01 portfolio and +25 only locally; at fixed margin +10 the later gap in the D01 coverage is closed and the new onset is 47.677. Several early gains also have substantial B0-only finite components; they are not credited to a local use of the contract at x<e^200.

## Factorial profiles and the analytic tail

Define for every integer k≥4
\[
 C_k=\sum_{i=0}^k \binom{k}{i} i!-\sum_{i=0}^k i!(k-i)!.
\]
At an onset in the next lists, \(Y>\sum_{k=4}^{j-1}C_k/L^{k-4}\) for every later real L. These are ordered by j, with first and last j indicated.

* j=7..20: 187, 211.5, 237, 263, 289, 316, 343, 369, 396, 423, 451, 478, 505, 535.
* j=21..40: 559, 587, 614, 641, 669, 696, 724, 751, 778, 806, 833, 861, 888, 916, 943, 971, 998, 1026, 1053, 1083.9.
* j=41..80: 1108, 1136, 1163, 1191, 1218, 1246, 1273, 1301, 1328, 1356, 1383, 1411, 1439, 1466, 1494, 1521, 1549, 1576, 1604, 1631, 1659, 1687, 1714, 1742, 1769, 1797, 1824, 1852, 1879, 1907, 1935, 1962, 1990, 2017, 2045, 2073, 2100, 2128, 2155, 2185.9.

Also add \(C_j/(2L^{j-4})\) for j=20,40,80 from L=546,1096,2197 respectively. B0-only secondary comparisons by the same general method: for j=80, onset 2889, and for its half-last-coefficient extension 2899. D01's half-C40 was from 1431. The paired B0 sufficient test for j=21 at L=559 fails by a large margin, whereas D02 closes the same profile there (same estimator, not an independent blind comparison). The high-order and low-order results use shared prime information, not independent numerical trials.

### The two-argument prime-count bounds

Write \(F_\pi(u)=u\pi(e^u)e^{-u}\), \(\Delta(u)=u[\pi(e^u)-\operatorname{li}(e^u)]e^{-u}\), \(m=\Delta-d_\theta\), with PV-li at zero. Let \(s=29.9\). Use the anchor and partial-summation identity in finite_anchor.md (PT PNT p.8, finite RH §3.3, CH2 Lemma 9.2 and Dusart Cor.4.5 at the anchor). For u≥40 set
\[
 D_d(u)=\frac{.155e^{-u/2}+2.6 J_d(u)e^{-du}}u+.074u e^{s/2-u}.
\]
Then \(-D_d(u)-2.36e^{-u/2}/u\le m(u)\le D_d(u)-1.9998, e^{-u/2}(1-e^{(s-u)/2})/u\). Indeed integrate \(g d_\psi\), \(g(v)=e^v/v^2\), by parts as \(-[g U_\psi]_s^u+\int g'U_\psi\). The low rates and the trivial term give the same charges as the old s=29.9 proof. For each positive exponential component of the high bound the rate a is ≤.3, so \((g e^{-av})'/(g e^{-av})\ge.7-2/s\), giving \(1+1/(.7-2/s)<2.6\). For the left boundary alone use the old crude \(3.2\cdot10^{-12}e^{-s/8}\) high upper bound (also valid with the stronger strip), so .074 is unchanged. The prime-power convolution has exactly the old two directed signs.

For \(d_\theta\) use the minimum of the finite RH θ leaf \(.0397888 u^2e^{-u/2}\) where eligible, and
\[
 -A(u)-(1.000000147)e^{-u/2}-1.78e^{-2u/3}
 \le d_\theta(u)\le A(u)-.9999e^{-u/2},
 \quad A(u)=\min(q+C_Te^{-u/2}, F_d(u)e^{-du}),
\]
where q and C_T are from D02_PROOF.md. This follows by subtracting \(\psi-\theta\) using Dusart Prop.4.3/Cor.4.5 PDF pp.12–13. Add the signed \(m\) interval; intersect with the old leaves rather than replacing on their domains. The original finite **π** bound, after normalizing, has a cube in u, not a square. At u≤43.7 retain the PT finite upper sign and the shifted-argument finite leaves.

For a factorial expansion of order N, \(H_N(u)=\sum_{i=0}^N i!/u^i\). Use
\[
 H_N(u)\le u\operatorname{li}(e^u)e^{-u}\le H_N(u)+V_N(u),\qquad
 V_N(u)=A_N u e^{-u}+\frac{B_N}{B_N-N-2}\frac{(N+1)!}{u^{N+1}}
\]
for u≥B_N. The verified pairs \((B_N,A_N)\) for N=20,40,80 are (40,170), (64,100), (128,11000). The checker evaluates the PV-li residual at B using \(c_0+\log u+\sum_{k\ge1}u^k/(k\,k!)\), with \(0<c_0<1\) as in ramanujan_repair.md, with 5 B terms and the geometric positive tail, and bounds the residual between 0 and A_N. Its derivative is \((N+1)!e^u/u^{N+2}\); integrate by comparison with \((e^u/u^{N+2})'\). For finite cells use the inherited order-20 anchor at 24 and improved V at 40 (no order-80 formula at early arguments).

If \(F_-,F_+\) are the positive lower and upper brackets for \(F_\pi\) (intersect eligible branches), the bracket for \(R L^2/x^2\) is
\[
 \frac L{L-1}F_-(L-1)-F_+(L)^2\ \,\le\,\,rac{R L^2}{x^2}\,\,\le\,\,
 \frac L{L-1}F_+(L-1)-F_-(L)^2.
\]
Apply the shift and square separately. At an analytic onset A the script freezes F_d and J_d at A−1. Dropping favorable signs gives the same positive error upper bound at u=L,L−1:
\[
 h_A(u)=\left(F_d(A-1)+2.6J_d(A-1)/u\right)e^{-du}
       +(1.000000147+2.515/u)e^{-u/2}+1.78e^{-2u/3}+.074u e^{s/2-u}.
\]
The upper π bracket uses \(H_N+V_N+h_A\), and the lower uses \(H_N-h_A\). The normalized lower-bracket debit is at most
\[
 \frac L{L-1}h_A(L-1)+e_L(2H_N(L)+e_L),\quad e_L=V_N(L)+h_A(L).
\]
The inputs are positive from the stated onsets by checking h_A(A−1)<1. Shift expansion of \(L H_N(L-1)/(L-1)\) has nonnegative coefficients; through N it gives the first sum in C_k. After squaring, terms through k=3 cancel, retain all C_4..C_N, and debit the square coefficients \(S_k=\sum_{i+j=k,0\le i,j\le N}i!j!\) at k>N. To prove the tail, subtract the chosen margin (including any fraction z of C_j) and multiply the remaining inequality in units \(RL^2/x^2\) by \(L^N\). Retained positive terms are nondecreasing, since \(z<C_j\). The square tail and the above scaled debit decrease in magnitude: \(N/A<d\), all other exponential rates are faster, \(u=L-1\) causes no adverse power except the numerator u in the fast anchor exponential, and V's inverse-power term has exponent N+1. Other positive factors are nonincreasing. Thus testing the sign at A in units \(L^j\) there proves the entire real tail. This proves bit-for-bit the inequalities implemented by end().

### Whole-cell coverage

Subtract the target polynomial symbolically and keep the lower deterministic part described above (N=20); on each closed cell [a,b] evaluate positive monomials on the right and subtract negative magnitudes from the left. Use the maximum eligible lower Δ and the minimum eligible upper Δ, with decreasing positive terms upper-bounded at the left. On [a,b] a negative term such as \(-.9999e^{-u/2}\) is upper-bounded at b, and the two factors of the signed upper convolution are bounded in the right directions using a and b. A left downward grid rounding of the argument of F_d in the certificate freezes **only the coefficient**, retaining the correct shifted/u exponent. If the unshifted upper error e is negative, verify \(H_{20}(b)+e>0\) and upper-bound the scaled square debit by \(a^j e(2H_{20}(b)+e)\); for e≥0 use \(b^j e(2H_{20}(a)+e)\). Multiply the shifted positive loss by \(b^j a/(a-1)\). The algorithm splits at all eligibility boundaries of its two arguments, and bisects a failed cell into *both* closed halves. Its finite success receipts cover the entire closed intervals, not just a set of x samples. Short-cell failures (listed later) are sufficient-test failures.

## An unbounded-order explicit lower profile

For constants c,A in the following table, for **every real L≥A** and **every integer n with \(40\le n\le L/c\)**,
\[
 Y>\sum_{k=4}^{n-1} C_k/L^{k-4} + C_n/(2L^{n-4}).
\]
In particular the comparison does not cease at order 80.

| premises | c | A |
|---|---:|---:|
|B0+D02|28|3000|
|B0+D02|27.8|6700|
|B0+D02|27.7|19000|
|B0+D02|27.65|190000|
|B0|38|3000|
|B0|37|12000|
|B0|36.9|40000|

Here is a separate simple derivation. For u=L or L−1 and n in the stated ranges, split li at \(e^{u/2}\), and use
\[
 ue^{-u}\operatorname{li}(e^u)=ue^{-u}\operatorname{li}(e^{u/2})+
 \int_0^{u/2} e^{-t}(1-t/u)^{-1}dt .
\]
Over the integration interval expand the denominator through k=n; the upper residual is at most \(2(n+1)!/u^{n+1}\). The omitted polynomial tail integral from u/2 to infinity is at most \(2e^{-u/2}/(1-2n/u)<3e^{-u/2}\): each \(t^k e^{-t}\) has log derivative ≤−(1−2n/u) on that tail, and \(\sum 2^{-k}<2\). The anchor contribution is positive and <\(4e^{-u/2}\) because \(H_{20}(u/2)+V_{20}(u/2)<2\). By the frozen π bound at A=3000, \(|\Delta(u)|\le e^{-du}\), and \(4e^{-u/2}<e^{-du}\). Thus
\[
 H_n(u)-2e^{-du} \le F_\pi(u)\le H_n(u)+2(n+1)!/u^{n+1}+2e^{-du}.
\]
Since \(n/u<1/27\), \(H_n\le27/26\), and the positive error is <.01 (the factorial ratio is at most \(u^{-2}\), by its first three factors and all others ≤1). Hence the square factor is <2.1. The shifted coefficient satisfies \(e^d L/(L-1)<1.18\). In units of \(n!/L^n\), the total cost is bounded by
\[
 \frac{4.2(n+1)}{L}+\frac{4}{L(1-2n/L)}
       +\frac{7e^{-dL}L^n}{n!}.
\]
The middle term comes from the square tail: for k>n both edge terms are absent, and \(\sum_{i=1}^{k-1}\binom{k}{i}^{-1}\le 2/k+2(k-3)/(k(k-1))<4/k\) (use the second binomial coefficient for all interior positions). Thus \(S_k\le 4(k-1)!\), and successive scaled tail magnitudes have ratio ≤2n/L. For k≥40 the same inequality gives \(C_k/k!\ge 1+1+1/2+1/6-(2+4/k)>1/2\). For 4≤k<40 exact small integer arithmetic gives positivity. Finally \(\log(n!)\ge n\log n-n\) by integrating log, and \(n(1+\log(L/n))\) increases with n≤L. Thus the last term is ≤\(7\exp[-(d-(1+\log c)/c)L]\). Each row uses a positive gap and the sum is <1/4 at its onset by directed checks, hence later. This is less than \(C_n/(2 n!)\). It is also valid to use the explicit cost test above for an individual eligible n if that is sharper. The limit of this proof has \((1+\log c)/c=d\); attempting c=27.6 yields the wrong sign for D02. This is a limit of the bound based on a uniform strip plus the factorial scale, not a claim of impossibility for the arithmetic gap.

## Early B0-only results and scope repair

The optimal sign domain remains **x>α**, α bracketed as in the archived candidate.md and exact local plateau proof there. At α there is equality, and the optimal integer onset is 38358837683. The independent finite bridge and the published DP Lemma 3.4 (arXiv:1407.1901v1 PDF p.10, not an RH conditional theorem) connect to the analytic positive ray. The original printed PT real finite sliver just above 38358837682 is refuted by the inherited local count; the original high sign ray from e^3915 remains valid. DP Theorem 1.3 remains conditional on full RH.

Smaller sufficient B0 onsets for constant Y margins .04, .30, .70, 1 are now 27.704, 28.17, 29.105, 30.577. At fixed L=27.8/28.3/29.2 the whole-ray margins improve to .098/.367/.734. Also \(Y>1.406\) on [34.3,43.7] and \(Y>1.037\) on [30.75,388]. Proof: early_new.py brackets the unnormalized li residual at the two ends via the exact PV series and uses its increasing derivative; the normalized residual is enclosed by multiplying with the opposite endpoints of the decreasing factor \(u e^{-u}\). On the common early finite domain combine the inherited signed Δ and shifted bounds; the sign-sensitive polynomial checks follow the preceding cell proof, including the negative-shift-loss case with opposite endpoints. The early .04/.30/.70/1 rows join their old later ray, and the fixed-onset gains join the stronger old .30/.70/1 rays, respectively. +1.037 to 191 uses a separate whole-cell certificate; to 221 the inherited B0 +16 quadratic profile dominates it, and from 221 through 388 use the B0 full quadratic.

**One inherited overbroad scope is false.** The archive's \(Y>1.03\) on *all* L≥30.75 (R-stronger-constant-3) cannot follow from its falling tail. Directed B0 upper bracketing at L=1000 gives \(Y<1.015\) (upper envelope <1.014147), a counterexample even without D02. Retain its certified finite result and improve to \(Y>1.03\) on **[30.714,477.005]**, B0 only. The early short check covers [30.714,30.75]; [30.75,388] follows from the +1.037 finite proof. For [388,477.005] the inherited B0 j=9 full degree-4 profile applies and exceeds 1.03 at the right endpoint (all profile terms decrease). The separately valid constant 1 ray is not removed. This correction applies wherever the archived summary, inherited registry, or review describes the invalid larger domain; exact archive bytes are not silently changed.

## Comparison and failed attempts

Use the pointwise maximum of all eligible lower margins and the pointwise minimum of all eligible upper brackets, including the B0 floor and usable original leaves. The finite 48–59 convolution is not replaced by the 27/32 contract. At the late plateau the conditional clipped density is usable around L=169, rather than the original-input switch near L=189. Around this joint shifted/unshifted switch a +80.8 or +81 connected proof fails even with up to 128 coefficient panels per unit and adaptive cells. This is a bottleneck of pointwise π-error debits: the two arguments currently pay essentially independent extremal errors, not a proof that R dips below either margin. A wider shift-correlation estimate would need more ordinate/phase information. The old .0397888 normalized direct π square is not reinstated. See recorded unsuccessful and successful trials; all asserted endpoints are sufficient except the established exact sign endpoint. No finite numerical sample is the proof of a real ray.
