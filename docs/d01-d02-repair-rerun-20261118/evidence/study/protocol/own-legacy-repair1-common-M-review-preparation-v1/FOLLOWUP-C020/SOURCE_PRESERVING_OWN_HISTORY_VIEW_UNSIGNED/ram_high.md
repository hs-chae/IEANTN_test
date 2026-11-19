# Higher-order Ramanujan lower profiles (B0)

Let \(L=\log x\), \(Y=L^6R(x)/x^2\) and
\[
C_k=\sum_{i=0}^k\binom ki i!-\sum_{i=0}^k i!(k-i)!\qquad (4\le k\le40).
\]
For \(j=21,\ldots,40\), strictly \(Y>\sum_{k=4}^{j-1}C_k/L^{k-4}\) for every real \(L\ge A_j\), with ordered onsets
\[
720,757,793,830,866,903,939,976,1013,1049,1086,1122,1159,1196,1232,1269,1306,1342,1379,1419.
\]
From \(L\ge1431\), add \(C_{40}/(2L^{36})\) to the sum through \(k=39\), with \(C_{40}=542983223118033629157634236574003452512389751201\). Thus the prior half-\(C_{20}\) term from 1000 is exceeded by the full \(C_{20}\) from 720. These are sufficient onsets, not optimality claims.

Use \(H_{40}(u)=\sum_{i=0}^{40}i!/u^i\). At \(u=64\) the unnormalized PV-li residual after \(e^uH_{40}(u)/u\) is between 0 and \(10^5\). The checker uses \(\log u+\sum_{n\ge1}u^n/(n\,n!)+c_0\), \(0<c_0<1\) as proved in ramanujan_repair.md, with \(n=240\), geometric tail and a directed 98-term exponential series at 1 raised to power 64. The derivative of the residual is \(41!e^u/u^{42}\). From 64, the derivative of \(e^u/u^{42}\) is at least \(11/32\) times the latter, so the normalized li is between \(H_{40}\) and \(H_{40}+V_{40}\), where \(V_{40}=10^5u e^{-u}+(32/11)41!/u^{41}\).

For \(L\ge A\) use \(|\Delta(u)|\le h(u)=C^*(A-1)e^{-u/8}+m^*(u)\) at \(u=L-1,L\) from ramanujan_repair.md and density_refine.md. In the \(RL^2/x^2\) normalization the error debit is
\[
\frac{L}{L-1}h(L-1)+e_L(2H_{40}(L)+e_L),\qquad e_L=V_{40}(L)+h(L).
\]
The lower inputs are positive: the losses decrease and \(h(719)<1\) (also checked by the script). In the deterministic part keep the positive expansion of the shift through 40 and subtract the square tail \(\sum_{k=41}^{80}S_k/L^k\) with \(S_k\) the coefficients of \(H_{40}^2\). The terms through 3 cancel and \(C_4,\ldots,C_{40}>0\) by exact arithmetic. Subtract the target and multiply by \(L^{40}\); the retained positive coefficient terms are nondecreasing including the residual at a half-coefficient target. The scaled negative tail terms decrease in magnitude. The scaled analytic losses likewise decrease, since \(40/L<1/8\) and this is the slowest exponential rate, a factor \(u\) occurs only in the fast exponential, and \(L^{40}/L^{41}\) decreases. The other nonnegative factors \(L/(L-1),H_{40},e_L\) are nonincreasing. Hence the strict rational check at \(A\) (equivalently in units \(L^j\) there) proves the full later real ray.

The first half-\(C_{40}\) trial mistakenly reused the much coarser absolute rounding floor of the order-20 program; the directed finer exponent calculation removes this numerical obstruction. The sufficient calculation at each selected integer onset minus one failed on scouting, not a counterexample to an earlier onset by another method. Keep the earlier depth-20 framework and its valid finite branches. All profiles share the same analytic prime bounds.
