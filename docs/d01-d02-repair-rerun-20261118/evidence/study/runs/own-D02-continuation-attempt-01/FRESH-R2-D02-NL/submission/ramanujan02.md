# Ramanujan gap: D02 portfolio

Let \(L=\log x,\ R=e x\pi(x/e)/L-\pi(x)^2,\ r=RL^6/x^2\). Use
\[
 Z_i=(i+4)!\sum_{j=0}^{i+4}1/j!-\sum_{k=0}^{i+4}k!(i+4-k)!,
 \qquad P_m(z)=\sum_{i=0}^{m-1}Z_i z^i .
\]
The first five coefficients are \(1,14,145,1412,13985\). All table inequalities are strict and real, including the onset.

## Results

* Retain the exact last real failure \(\xi\) and sharp integer onset 38358837683 (ramanujan.md). On \((\xi,38358837683)\) one also has the exact profile \(R=632207037\,e x/L-1644673232^2\). No claim of unconditional literal real positivity from just above 38358837682 is made: the reported early *integer* result from Platt–Trudgian Thm. 2, PDF p. 3, is used as in the inherited proof. The real-domain correction and sign bridge overlap all new bounds; D02 cannot improve the true sign onset.
* RAY PASS in window_b0.txt and window_d2.txt gives a strict lower polynomial in \(1/L\) from the listed real logarithmic onset on the entire ray, under \(B_0\) and \(B_2\) respectively. WINDOW PASS gives the displayed closed interval only. All D01 floor branches remain. Already under \(B_0\) standalone analytic positivity starts at 36.60 without the published early prime-count computation; at 36.85 the margin becomes .06 instead of .03, and at 40.5 it becomes .54 instead of .50. Margin .50 holds from 40.3 and margin 1 from 42.7. On the earlier separated interval [39,39.47] the margin is .77. The third coefficient 145 is proved on [54,125]; \(1+14/L+145/L^2+1100/L^3\) on [58,104]. These improvements are input-independent.
* Under D02, at fixed onset 50 one can use \(1+14/L+81/L^2\) on the entire ray, and at 49.8 the third coefficient is 75; at 49 it is 44. Stronger early bounded profiles are kept (e.g. coefficient 99 on [50,160]), but do not cross the intermediate valley. A \(B_0\) connected ray uses coefficient 16 from 48. At fixed coefficient 145 the later connected ray starts at 185.6 vs 216.7, in addition to the early window. This is a comparison of certified bounds, not a failure claim about the actual gap.
* ORDER rows of order_b0.txt / order_d2.txt have columns cap, m, auxiliary degree N, sufficient onset J for \(r>P_m(1/L)\) on all \(L\ge J\). COEFFICIENT rows give a coefficient tuple and its onset. At \(L=600\), for instance, at least 16 coefficients are certified with D02 versus 13 in the matched original-input calculation. Example fixed-margin comparisons:

  | m | \(B_0\) onset | \(B_2\) onset |
  |---:|---:|---:|
  |3|216.7|185.6|
  |4|249.7|210|
  |5|283.8|235.3|
  |8|389.5|313.9|
  |10|461.3|367.4|
  |16|678.9|530.1|
  |24|971.2|748.9|
  |32|1264.3|968.5|
  |40|1557.8|1188.5|
  |72|2734|2070.3|
  |96|3616.9|2732.5|

* Growing-order result: in the following rows let \(m=\lfloor L/a\rfloor\). Then \(r>P_m(1/L)\) on the entire real ray \(L\ge am_0\), including transitions of m.

  | premises | a | \(m_0\) |
  |---|---:|---:|
  |\(B_2\)|32|40|
  |\(B_2\)|30|75|
  |\(B_2\)|29|145|
  |\(B_2\)|28|570|
  |\(B_0\)|42|55|
  |\(B_0\)|40|70|
  |\(B_0\)|39|120|

  Retain also the inherited effective theorem for any fixed number of coefficients.
* Let \(A(u)=ue^{-u}\operatorname{li}(e^u)\) in the original principal-value convention and \(\mathcal H(L)=L^4([L/(L-1)]A(L-1)-A(L)^2)\). On \(L\ge176\) we have the two-sided errors
\[
 |r-\mathcal H(L)|<.048L^4e^{-L/8}\quad(B_0),\qquad
 |r-\mathcal H(L)|<.87L^4e^{-5L/32}\quad(B_2).
\]
The latter error bound is strictly smaller on the whole matched ray since \(.87e^{-176/32}<.048\). The signed π bounds below yield a still stronger pointwise lower branch. Take the maximum of every applicable new and inherited branch; strictness holds if a strict branch realizes that value. See comparison02.md for matched-envelope comparisons.

## Signed π transfer (both arguments L and L−1)

Use (3) of ramanujan.md with \(|K_{20}|<400000\). If \(w(t)=e^t/t^2,\ I_1(u)=\int_u^\infty v(t)dt\), the \(\psi\)-error integral is
\[
 w(20)I_1(20)-w(u)I_1(u)+\int_{20}^u w'(t)I_1(t)dt .
\]
This uses the compact absolute continuity of \(I_1\). The first factor \(w(20)|I_1(20)|<3\) by analytic02.md. On \(t\ge20\), \(0\le w'\le w\); for a constituent \(g e^{-dt}\) of the integrated error with \(d<.9\), \(w(t)e^{-dt}\) grows with logarithmic slope at least \(1-d-.1\). Thus its last two contributions after normalization are at most \(g e^{-du}/u\,(1+1/(1-d-.1))\). Use \((g,d)=(.0503,1/2),(5.8\cdot10^{-12},c)\); for \(d=1\) use \(1.84e^{-u}(1/u+u/20)\), since \(\int_{20}^u dt/t^2\le1/20\). Sum with \(400003 u e^{-u}\), incorporating both anchors, to obtain \(U_b(u)\).

Taking \(V_b\) to be the available minimum of ψ endpoint bounds (analytic02.md, inherited bounds, finite-height adaptive CH, and direct D02 only at \(u\ge200\)), the lower normalized π discrepancy is bounded by the negative of
\[
 V_b(u)+U_b(u)+
 \sum_{(g,d)=(1.000001,1/2),(1.78,2/3)}
        g e^{-du}(1+1/((1-d-.1)u)).
\]
The upper discrepancy is bounded by \(V_b+U_b-.9999e^{-u/2}\), because \(-P_\theta\) has nonpositive sign in the integral and its endpoint is bounded above by \(-.9999e^{-u/2}\). For qosc, weaken any negative upper result to zero and use the inherited one-sided π sign where available. For a compact cell the subtracted exponential uses the right end. The additional positive-term branch termq uses (3) at J: for \(u^m e^{-du}u/(u-M)\) the log slope of the integrand majorant is at least \(1-d-(2-m)/J-M/[J(J-M)]\), omitting the last term if \(M=0\). The anchor contributes at most \(u/J\ e^{J-u}[q_c(J)+(\mathrm{CH}+P)(J)]\) in normalized units, by common.md and the inherited absolute transfer \(q_c\).

With \(q_-,q_+\) bounding the two signed discrepancies, (2) of ramanujan.md gives \(r\ge L^4([L/(L-1)](A(L-1)-q_-(L-1))-(A(L)+q_+(L))^2)\). The square bounds a nonnegative prime count. The absolute version and the triangle inequality give the two-sided model error: global02.py checks normalized absolute π error \(<.015e^{-u/8}\), \(<.270e^{-5u/32}\), respectively, for \(u\ge175\), by decreasing scaled functions and the bound at 175. Then \(0<A(L)<1.01\) for \(L\ge176\) by the 20-term expansion below, and the shift costs \(e^c L/(L-1)\) applied at 176. Checks enclosure the exponentially decaying square term as well.

## Polynomial certificate

For N=20 use the exact inherited anchor \(V=24\). Otherwise use \(V=2(N+2)\), \(S_N=\sum_{j=0}^{N}j!/u^j\). The absolute anchor difference \(|\operatorname{li}(e^V)-e^VS_N(V)/V|<5 e^V\), since \(S_N(V)\le2\) and the Ei series in ramanujan.md gives \(|\operatorname{li}(e^V)|\le1+\log V+e^V-1\). The residual integral from differentiating is \((N+1)!\int_V^u e^t/t^{N+2}dt\); its log-slope estimate bounds it between 0 and \(2(N+1)!e^u/u^{N+2}\). Denote by \(r_N\) the normalized upper residual with factorial part \(2(N+1)!/u^{N+1}\) (12 instead of 2 for N=20) and anchor part \(H_0u e^{-u}\), where \(H_0=5e^V\) or 10 respectively. The lower residual is at least \(-H_0u e^{-u}\).

Apply (4) of ramanujan.md with this N and upper \(t=r_N+q_+\). Expanding the shifted binomial through degree N and dropping all higher positive terms yields the \(Z_i\); the penalty is the high convolution plus
\[
 L^4[2S_N(L)t+t^2+H_0 L e^{-(L-1)}+(L/(L-1))q_-(L-1)] .
\]
For each closed cell use its right end for \(L^4\) and positive residual coefficients, its left end for negative residual coefficients and for the individually decreasing error factors. An endpoint branch with finite upper domain is used only if it covers the whole cell. Shift the cell itself when bounding \(q_-(L-1)\) and split the sign boundary. Recursive subdivision covers compact intervals, not a grid of sampled values.

For the analytic tail, choose one fixed admissible positive-term bound at J and for both shifts. When all coefficient residuals are nonnegative, scale the full penalty and residual polynomial by \(L^{N-4}\). All retained residual monomials become nondecreasing. Each exponential penalty constituent decreases by the guard \(N+m\le d(J-1)\); the anchor guard is \(N+1\le J-1\); the factors \(1+1/(\delta u),u/(u-M)\) decrease. This also handles the square by attaching the scaling to one factor. The scaled factorial and higher convolution penalties decrease. A strict comparison at J proves the entire tail, including the join if J is the last endpoint of a compact certificate. This uses every nonnegative coefficient residual, not just the first one. Search tests sufficient onsets, not necessity.

## Growing-order certificate

Take \(m=\lfloor L/a\rfloor\), \(N=m+12\), \(V=2m+28\), so the anchor works also at \(L-1\). Use absolute q bounded by \(e^{-cu}\) for \(u\ge175\). For \(L\ge am\), \(S_N\le2\) and \(t\le1\) by
\(2(2/a)^{m+13}+5L e^{2m+28-L}+e^{-cL}<1\), checked at \(L=am,m=m_0\) and decreasing thereafter. For \(j>N\), \(C_j\le3j!\) since the full convolution divided by \(j!\) is at most \(2+2/j+2(j-3)/(j(j-1))\), by bounding inverse binomial coefficients. Bounding the higher convolution by a geometric series of ratio \(2N/L\) gives total penalty at most
\[
 15(m+13)!/L^{m+9}+7L^4e^{-c(L-1)}+35L^5e^{2m+29-L}.
\]
The omitted \(Z_m\ge(m+4)!/2\): the normalized shifted sum is at least \(65/24\) and the normalized convolution is \(\le2+4/(m+4)\). Divide the penalty by \((m+4)!/(2L^m)\) and use \((m+4)!\ge m^4(m/e)^m\) by integrating log. The scaled terms attain their upper bounds when \(L=am\), since \(acm\ge m+4,\ am\ge m+5\). The resulting ratios are bounded by
\[
 30(2/a)^9,\qquad 28a^4(ae^{1-ac})^m,\qquad 70e^{29}a^5m(ae^{3-a})^m.
\]
global02.py checks sum \(<1\) at \(m_0\) and decrease in subsequent integer m. Thus no sampled or unverified part of the variable-degree ray remains.

## Limitations and serious trials

At the true real onset, counts determine the sign. The stronger cap is most useful in the intermediate and deep-order regions; early lower π at \(x/e\) still needs finite-height information. The \(B_0\) connected trial with third coefficient 20 from 48.5 fails to certify near log 186.5; D02's with 82 from 50 fails near 168.3, near the crossover of the CH floor and D02 density estimate. The bounded fourth-coefficient trial 1250 failed around 100 under both caps; 1100 was retained instead. These failures are not counterexamples. The initial trial with fifth coefficient 15000 is false as an eventual profile: its first excess coefficient is larger than 13985, and expanding the model one more term with its exponential error proves it eventually exceeds the normalized gap. It was repaired with 13000. A finer upper bound for the endpoints or another finite-range localized π certificate would be needed to push the demonstrated valleys and earliest margins; no global optimality is asserted.
