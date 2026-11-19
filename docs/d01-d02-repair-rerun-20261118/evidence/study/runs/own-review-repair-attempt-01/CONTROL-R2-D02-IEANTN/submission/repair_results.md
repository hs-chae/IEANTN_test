# D02 own-review repair and strengthened certificates

This is a continuation of FOLLOWUP-C016 under the same premises, not a new baseline. B0 means the original packet; B1 adds the exact all-real `PsiMajorant` for $x\ge e^{200}$ with coefficient $1/64$, exponent $27/32$, and log power 2. None of the own review computations is used as a new premise. Combine this supplement with the **entire** prior portfolio, with the corrections below. Ordinary executable proofs are not Lean or source-first PV.

## 1. Three missing reciprocal-sum joins, now certified

For $L=\log x$, write $\mathcal R=\sum_{p\le x}1/p-\log L-M$, with $M$ exactly Dusart2018 p.17 Thm.5.6 (pinned text LF 1482–1496). All entries below assert $|\mathcal R(x)|\le c/L^3$ for **every real** $x$ at least the stated decimal, inclusively. These are B0 branches also retained on B1.

| $c$ | Previously printed (old evidence insufficient) | Old supported receipt | New certified |
|---:|---:|---:|---:|
| .2 | 2278382.186 | 2278382.271 | **2278382.113** |
| .15 | 5001781.860 | 5001782.058 | **5001781.694** |
| .12 | 8789120.961 | 8789121.321 | **8789120.657** |

The three newly proved rays include each previously missing half-open interval. The original assertions are therefore true at this trust tier, but remain unproved by the original certificate alone. For exact historical bytes see `prior_mertens.md` and `sieve_receipt.txt`. The new cutoffs for *all 17* reciprocal rows are printed as integers in the **new** column of `repair_m_receipt.txt`; divide by 1000. In particular .0223 holds from $613281283$, inclusive. None of these replacements is claimed to be optimal.

### Improved independent enclosure for $M$

Put $K=10^8$, $Y=10^{13}$, $f(t)=\sum_{m\ge2}1/(mt^m)$ and $g(t)=f(t)/\log t$ for $t>1$. Determine
$$
 M=\gamma-\sum_{p\le K} f(p)-T,\qquad T=\int_{(K,\infty)}g(t)\,d\theta(t).
$$
For the finite sum, `repair_m.cpp` uses Eratosthenes. At each prime, sum $\lfloor U/(mp^m)\rfloor$ for all $mp^m\le U=2^{100}$. The omitted terms sum to less than $2/U$ per prime since successive summands have ratio less than $1/p\le 1/2$; each retained floor loses less than $1/U$. The printed endpoints pad by the number of retained terms plus twice the prime count. Integer widths suffice: $p\le10^8<2^{27}$ in the power loop, $m\ge2$, so even the subsequent multiplication has $qp\le (U/2)p<2^{126}$; the tested product $qm$ is formed only after passing $q\le U/m$. The total $f$-sum is less than $1$ by $f(t)\le1/(2t(t-1))$ and telescoping over integers. The sieve ceiling is at most $2\cdot10^9$, as are the original 32-bit bounds on loop indices including their last increments. Reciprocal-sum snapshots use one floor at $2^{62}$ per prime and the prime count as padding.

For $\gamma$ use $n=10^6$ and $\gamma=H_n-\log n-1/(2n)+E_n$, where $|E_n|\le(n-1)^{-2}$. Indeed, summing the unit trapezoid differences from $\int dt/t$ from $n$ up gives $E_n$, with each error at most $1/(6k^3)$ on $[k,k+1]$ by integrating the linear interpolation bound with $\sup |(1/t)''|$. Enclose $H_n$ by floors at $2^{62}$ padded by $n/2^{62}$. No external decimal digit of $\gamma$ or $M$ is assumed.

Let $B=\int_K^\infty g(t)dt$, and (J=\int_K^\infty [2t^2\log t]^{-1}dt). Then $J\le B\le(1+2/[3(K-1)]$J) by summing the geometric majorant for $m\ge3$. With $h=\log K$,
$$
 J=\frac{1}{2K}\int_0^\infty\frac{e^{-u}}{h+u}\,du .
$$
The finite geometric identity for $1/(h+u)$ gives inequalities, for every $u\ge0$, between the 14- and 15-term expansions, respectively below and above. Integrating them gives the alternating factorial sums in `repair_m.py`; no use of a convergent infinite factorial expansion is made.

For $K\le t\le Y$, CH2 p.35 Lem.9.2 and Dusart2018 p.13 Cor.4.5 give
$$
 |\theta(t)-t|/t\le 1.791000147/\sqrt t+1.78/t^{2/3}<.000188.
$$
For $t\ge Y$, Dusart p.11 Thm.4.2's global $k=3$ row gives $20.83/\log^3 t<.001$. Let $G(t)=(1+2/[3(K-1)]$/$2t^2\log t$) for $t\ge K$, so $g\le G$. Integration by parts with the right-continuous counting function gives
$$
 |T-B|\le .000188 (2K G(K)+B)+.001\cdot2Y G(Y).
$$
In detail, the boundary at $K$ costs at most $.000188 K g(K)$; the first integral costs at most $.000188\int_K^\infty t(-g'(t))dt=.000188(Kg(K)+B)$. The part with the later error bound costs at most $.001(Yg(Y)+\int_Y^\infty g)$; the last integral is at most $YG(Y)$. The boundary at infinity is zero by these same bounds. This yields
$$
 .26149721284629719<M<.26149721284881525.
$$
The program uses the narrower full directed interval in the receipt. The previously attempted .000181 relative cap at $K$ failed its outward check; .000188 is checked, not assumed.

### Entire-domain link

Let $a,b$ be the last uncertified endpoint and its next prime for an old receipt row, and $x_0$ the old sufficient cutoff. The new sieve verifies both primes and *absence* of primes in $(a,b)$, and encloses the sum through $a$. Search inside $[a,x_0]$ for a new certified $y$ at milligrid resolution. Only the **final directed test** at $y$ is used, so search monotonicity at finite precision is not required. On $[a,b)$, the true $\mathcal R$ has derivative $-1/L$ in $L$, so both $\mathcal R-c/L^3$ and $\mathcal R+c/L^3$ strictly decrease because $L^3>3c$. Thus the upper inequality follows from its value at $y$ and the lower inequality from its value at $x_0$, if $x_0<b$, or by the old left-limit certificate at $b$ otherwise. The executable test at $x_0$ also uses the pre-$b$ sum, so covers that limiting situation equally. If $y=a$, the sum used includes $a$, as required for the inclusive endpoint. For $[x_0,\infty)$ use the old fully joined ray. This proof fixes the uncertainty of the constants, not a jump convention. It requires no assertions about the true magnitudes at an uncertified endpoint, or prior to $a$.

## 2. New Mertens envelope branches

At coefficient .02214 the strengthened **B0** inverse-log branches start at these inclusive real cutoffs: both relative product errors at $615211905.922$ (bound $.02214/L^3$); $|\mathcal R|$ at $615614013.682$ (same bound); $|\mathcal G|$ at $1110171343.327$ (bound $.02214/L^2$). These do not displace earlier domains with larger coefficients.

* The generated fixed-point source from `sieve14.py` changes only the target list of the original `mertens.cpp`, to $2214/100000$ in each of the three forms. Thus the bounded integer arithmetic, both sides of jumps, monotone prime-free interpolation and terminal check at $N=2\cdot10^9$ are precisely the original proof in mertens.md §6. The first seven lines of the new sieve receipt are identical to those of the old one.
* `anchor.py` now actually rounds the positive product pad **upward** at working precision in the near-$N$ signed check. Its corrected run is byte-identical to `anchor_receipt.txt`; the old byte sequence for the source is preserved in `prior_anchor.py`. `bridge14.py` retests the corrected full analytic bridge with strict budget .02214 for each observable, with the same authenticated $N$ anchors. Maxima are below .022130 through $L=23.3$ and below .022113 through $L=29.9$, with separate tested blocks up to 200. For $L\ge200$, the B0 clean .01880 bound applies and $.01880 L^2e^{-L/8}$ decreases and is $<.02214$ at 200. The rays therefore include every join and the whole tail.
* Real exponent comparisons retain the main M6 curve (from $L\ge62$), all original branches and the exact signed prescription in mertens.md §5. `m_tail_extra_receipt.txt` adds rounded whole-ray M0 coefficients (first three errors (C x^{-a}/L), weighted error (C x^{-a})): B0 $(L_0,C)=(155,.22320),(200,.018791)$; B1 ((155,.51687),(169,.32619),(200,.25973)). At the common onset 200 the ratio $(.25973/.018791)e^{-L/32}$ is already strictly less than 1 and decreases. Moreover $.25973e^{-L/32}<.01$ there, so B1 still beats the established B0 spectral budget floor throughout the common ray. Reusing the M6 ray monotonicity rather than inferring a tail from the grid, fixed error $10^{-14}$ for products and reciprocals is certified from $L=1485/8$ (B0) versus $2667/16$ (B1); weighted $10^{-12}$ from $190$ vs $1357/8$. These are sufficient values, not optimal onsets.

**Stronger per-observable bridge:** on B0, again with inclusive real endpoints, both product errors are at most \(.02209/L^3\) from \(615614452.413\), the reciprocal error is at most \(.02209/L^3\) from \(615616274.570\), and the weighted error is at most \(.02127/L^2\) from \(1122442236.136\). These and the .02214 rows are separate strength/onset tradeoffs.

The finite sieve changes only the target list as above; `sieve_opt_receipt.txt` gives the endpoints and the unchanged anchor. For the continuation, the same signed argument for `anch` is legal through \(L=24\): \(e^{24}<10^{13}\), the \(.19e^{-v/2}\) signed estimate is verified at \(\log N\) and remains valid by monotonicity of \(d(v)=166.64/v^3\), and the other CH2 and prime-power terms hold on this full interval. The `after` branch is legal already at \(N\) since the \(.791\) seed and the earlier exact-\(K\) transport need only \(10^4\le x\le e^K\). Instead of switching all observables at 23.3, take the **minimum separately** for each observable of the two block bounds on \([\log N,24]\). This yields checked block maxima below .022084, .022084, .021266 in the three normalizations. Through 200 use `after` on the same split domains and the finer \(1/128\) grid; beyond 200 use \(.01880L^2e^{-L/8}<.02127\) and its monotone decrease. No estimated crossing is asserted as a valid switch. Exact executable certificates are `bridge_opt.py` and `sieve_opt.py` and their two receipts.

The early inverse-log improvements get no D02 credit. The B1 power/onset differences arise solely from lowering the cap to $27/32$ in the absolute high-zero budget before transport. Use the per-observable **pointwise minimum** of all earlier and new legal bounds, retaining the signed intervals when stronger. Comparison is with the same-operator B0 portfolio and the original bounds on their actual domains, not with an unspecified optimum over all B0 proofs.

## 3. Higher Ramanujan profiles and lower sufficient onsets

Let $r=L^6R(x)/x^2$, $H_N$ as in ramanujan.md. The rows assert strict inequalities for **every real** $x$ with $L$ at least the stated inclusive cutoff.

| Strict lower profile | B0 $L_0$ | B1 $L_0$ |
|---|---:|---:|
| $1+14/L+100/L^2$ | $3199/16$ | $2749/16$ |
| $H_6$ | $3529/16$ | $2987/16$ |
| $H_{26}$ | $1879/2$ | $1447/2$ |
| $H_{27}$ | 976 | 751 |
| $H_{30}$ | 1086 | $1667/2$ |
| $H_{35}$ | $2539/2$ | 971 |
| $H_{40}$ | 1453 | $2217/2$ |
| $H_{45}$ | $3273/2$ | 1246 |
| $H_{50}$ | 1820 | $2767/2$ |
| $H_{55}$ | $4007/2$ | $3043/2$ |
| $H_{60}$ | $4375/2$ | 1659 |
| $H_{65}$ | $4743/2$ | 1797 |
| $H_{69}$ | $5037/2$ | 1907 |

All original fixed margins, $H_N$ rows, finite branches, and the connected sign result stay in the maximum. The original real sign endpoint remains $(38358837682+u,\infty)$ for the permanent strict ray, with the exact root and bracket in ramanujan.md §1. The analogous finite result from Dudek–Platt p.10 Lem.3.4 remains inherited at the stipulated original-paper computation tier, not independently recomputed; the displayed generic stepping lemma in that paper does not automatically bound fractional prime-count increments, so no new conclusion relies on applying that proof argument to arbitrary fractional steps. The local failure of the literal real onset of Platt–Trudgian's PNT Thm.2 remains a documented counterexample, not a failure of our connected domain.

**Higher barrier.** Reuse R2's same integrating-factor/positive-polynomial criterion with $N=70$, $L_0=95$; positivity of all $g_4,\dots,g_{70}$, the exact polynomial residual test and strict sufficient initial tests are replayed. The antiderivative used for the new initial check is $\log s+\sum_{j\ge1}s^j/(j\,j!)$. On $0<s\le100$, after term 512, subsequent ratios are at most $100/513<1/2$, so the remainder is at most twice the first omitted term. Some earlier starts failed in this implementation; e.g. the initial $P_{28}$ test at 34 and smooth $C$ test at 35 failed. These do not rule out better barriers. $L^4C>H_{70}$ holds for $L\ge95$.

**Oscillatory tail.** At $v\ge62$, use the oscillatory transport of ramanujan.md §4 for $Z_b$, and transport $D_b$ plus the two Dusart power corrections by the ordinary positive kernel from 62. The previous integral $\int_{\log600}^{62} e^t|E_\theta(t)|dt/t^2$ is bounded by $2e^{29}/25$ through 58 and by $4e^{62}[J_{\rm CH}(58)+1.000000147e^{-29}+1.78e^{-116/3}]/58^2$ above 58. The extra lower boundary of the oscillatory integration contributes the constant $e^{62} Z_b(62)/(H62^2)$ to the same integral budget. Thus the function `osc` is a bound for $v^4$ times absolute R1 error, and `osc_loss` is the corresponding loss in R3. Each piece has the form of a positive constant times $v^k e^{-av}$ times a positive decreasing factor, where $k\le8,\ a\ge1/8$.

For target $H_K$ take $j=K-3$ and compare the loss rescaled by $L^j$ with $g_{K+1}$, dropping the other positive residuals. Once $L-1\ge8(8+j)$, each such rescaled budget decreases in $L$. For the shifted term apply the threshold to $v=L-1$ and keep the extra decreasing ratio $(L/(L-1))^{5+j}$. For the linear unshifted term $U_A$ decreases, and the squared term factors into rescaled $d$ times the decreasing $d/L^4$. The checked half-unit onsets thus certify the entire rays. The same test with $j=2$, $g_{K+1}$ replaced by 45, handles the 100-target tail, and $j=3$ with $g_7$ handles the $H_6$ tail. Before those tail thresholds, use $H_{27}$ and cover each closed rational block: each positive residual at its right endpoint, the minimum of the prior block loss and the decreasing oscillatory loss at the left. Bisection proposes onsets only, while the exact block/tail validations certify them. The demonstrated gain from oscillation in the $H_{26}$ endpoint is small; the principal higher-order gain is allowing a much deeper smooth barrier, and the matched-assumption gain is from the stronger cap, not the deeper smooth barrier.

**Matched fixed onset.** For all real $L\ge49.1$, the margin $1+14/L+c/L^2$ is now certified for $c=15/2$ on B0 and $c=799/10$ on B1. For each block before 240, `fixed49.py` takes the positive residual $H_{27}-(1+14/L+c/L^2)$ at the right endpoint. It transports the CH2 (9.4) bound from ramanujan.md §4 through $L=58$, then uses the B0/B1 budget of `cert.py` on the remaining blocks (including its shifted-argument join). A block with insufficient slack is bisected until a directed test passes or the computation rejects at its mesh limit. This covers $[49.1,240]$ with closed blocks; the ordinary spectral-only scaled residual test applies from 240. B1 acts only in the later budget, not in the initial CH2 computation. Without extending the optimized-height CH2 branch beyond 49.4, the 79.9 choice failed near that endpoint; extending the branch to the already legal 58 fixes the finite join. The $c=7.7$ B0 trial failed a narrow sufficient test on $[484079/2560,968163/5120]$ (near the CH/spectral switch). Neither failure is a counterexample to the true gap.

## 4. Reproduction, provenance, and remaining bottlenecks

`replay_repair.sh` gives the executable commands and byte linkage. `notes.md` gives the original replay, interval arithmetic contract and earlier serious attempts. `claim_map.json` accounts for the complete 142-object historical list with exact prior-byte hashes and current claim links. The original endpoint, early, Ramanujan, Mertens, and full two-billion sieve computations were also rerun here and matched all five old receipts byte for byte, in addition to the corrected anchor replay. The pinned source SHA-256 pairs were rechecked against the supplied index; the source locators in the legacy proofs remain in force. In particular FKS p.4 uses $\beta\ge s, 0<\gamma<t$, corrected in the current spectral text; restriction to $\beta>s$ and the continuous right limit in $t$ were already mathematically safe. No other paper conclusions are silently re-normalized. The original exact edited bytes are preserved as `prior_*`; all original receipts and untouched proof/code files are retained.

Going earlier than the checked prime-free interval would require a new scan before the previous bad endpoint (or a more powerful arithmetic method); the repair does not extrapolate past that endpoint. For products or reciprocals a coefficient .0220 still fails the optimized near-anchor block budgets, not necessarily the underlying inequalities. The weighted branch instead uses the separately checked .02127. The late decay budgets remain limited by certified control of the high zeros near the cap; no line exclusion or sharp constant is claimed. Extending trusted sign verification independently of Dudek–Platt's published finite computation would require new large-scale exact work and is not accomplished by the local quotient sieve. All reported changes preserve the separation between exact arithmetic, rigorous block/tail checks, analytic inequalities and inherited original-paper results.

**Accounting:** planned own-review repair. The index records prior research 94,250 generated tokens, with reviewer work excluded. This turn's separate repair work includes source/identity audit, new integer and interval programs, whole-domain transfer proofs and replays; authoritative repair-token totals were not exposed. Cumulative count is the recorded prior 94,250 plus actual repair generation, excluding reviewer tokens, not a reset or an estimate. The initial command did print cwd but lacked `ls` (exit 127); Python enumerated and read the two files immediately thereafter. Missing locale warning did not affect the work. No execution interruption was used to explain a mathematical gap.
