# Finite π correction and replacement convolution (B0)

FOLLOWUP-C020's finite RH **π** leaf used the wrong normalization. Corollary 1 of PlattTrudgianFiniteRH, original PDF p.4, extraction lines 147–150, bounds the absolute π error by \(\sqrt x\log^2 x/(8\pi)\). Thus the normalized leaf for \(\Delta(u)=u(\pi(e^u)-\operatorname{li}(e^u))e^{-u}\) is \(cu^3e^{-u/2}\) throughout \([26,58]\), not \(cu^2e^{-u/2}\). The smaller direct leaf R-pi-finite-log2 is retired, not declared false. The printed **θ** line does give the square for the relative θ error. Simply correcting the cube in the C020 checker fails the +8 connected sufficient comparison at \(L=47.7\). Use the following repair.

For \(s\le u\), put \(m(u)=\Delta(u)-d_\theta(u)\), \(P(v)=(\psi-\theta)(e^v)e^{-v}\), \(d_\psi(v)=\psi(e^v)e^{-v}-1\), \(g(v)=e^v/v^2\). Partial summation gives
\[
m(u)=\frac us e^{s-u}(\Delta(s)-d_\theta(s))
      +u e^{-u}\int_s^u g(v)(d_\psi(v)-P(v))\,dv .
\]
The primitive \(U(v)=\int_v^\infty d_\psi(t)\,dt\) is locally absolutely continuous. Use d01_smooth.md S1 (CH2 (B.9), PDF p.46; low reciprocal sum <.0463), and the high-tail bound of d02_smoothing.md at strip \(1/8\), giving \(|U(v)|\le .0463e^{-v/2}+3.2\cdot10^{-12}e^{-v/8}+2e^{-v}\). On \([s,u]\) integrate \(g d_\psi\) as \(-[gU]_s^u+\int g'U\), with \(0\le g'\le g\). For \(a=1/2,1/8\), the derivative of \(g(v)e^{-av}\) is at least \(r_a=1-a-2/s>0\) times itself. Thus the integral and upper boundary pay a coefficient \(1+1/r_a\) for the corresponding endpoint terms, plus a lower boundary. The trivial term contributes at most \(2u e^{-u}(1/s^2+1/u^2+1/s)\), since \(\int_s^u v^{-2}dv\le1/s\). If the anchor error is at most \(A_s e^{-s/2}\), all constant-anchor charges are paid by the coefficient
\[
 A_s/s+(.0463+3.2\cdot10^{-12}e^{3s/8}+4e^{-s/2})/s^2+2e^{-s/2}/s
\]
multiplying \(u e^{s/2-u}\). This includes both trivial boundaries.

By Dusart Prop. 4.3 and Cor. 4.5 (PDF pp.12–13),
\(.9999e^{-v/2}\le P(v)\le(1.000000147+1.78e^{-s/6})e^{-v/2}\) for \(v\ge s\). Its convolution from the lower bound, using \(v^{-2}\ge u^{-2}\), is at least \(1.9998 e^{-u/2}(1-e^{(s-u)/2})/u\); the upper convolution uses \(r_{1/2}\). Subtract it with the correct sign.

At \(s=29.9\), the PT finite π quotation (p.8, with normalization allowance as in ramanujan_repair.md), finite RH §3.3 p.5 and CH2 Lemma 9.2 p.35 give \(-B(s)\le\Delta(s)\le0\), \(-1.84e^{-s/2}\le d_\theta(s)\le-.2089e^{-s/2}\); hence \(A_s=2.2\) suffices. The above constants pass the directed tests in ram_repair.py and give a useful two-sided enclosure:
\[
D(u)=(.155e^{-u/2}+7.2\cdot10^{-12}e^{-u/8})/u+.074u e^{s/2-u},\quad
-D(u)-2.36e^{-u/2}/u\le m(u)\le D(u)-1.9998e^{-u/2}(1-e^{(s-u)/2})/u.
\]
At \(s=18\), \(A_s=2.04\) (signed early anchor in ramanujan_repair.md). The same proof, dropping the negative upper prime-power term, gives
\[
D_{18}(u)=(.166e^{-u/2}+7.5\cdot10^{-12}e^{-u/8})/u+.114u e^{9-u},\quad
-D_{18}(u)-2.81e^{-u/2}/u\le m(u)\le D_{18}(u),
\]
as checked in m_postreview.py. This latter result is used only for Mertens here.

For Ramanujan use the \(s=29.9\) transfer from \(u=40\). The local relative θ cap is \(q+(114.671+1.78e^{-u/6})e^{-u/2}\) by CH2 Cor.1.3 p.3 and Dusart, \(q=1.047198\cdot10^{-12}\); take its minimum with \(cu^2e^{-u/2}\) on \(40\le u\le58\), now sourced correctly from finite θ. Add the signed \(m\) interval on the respective sides. For \(27\le u\le29.9\) also strengthen the early \(-.17e^{-u/2}\) bound for \(\Delta_+\) using the partial sum anchored at 18 and the same elementary lower convolution against the negative \(d_\theta(v)\):
\[
\Delta(u)\le-.2089e^{-u/2}+1.84(u/18)e^{9-u}-.4178e^{-u/2}(1-e^{9-u/2})/u.
\]
All inequalities allow inclusive prime counts; the integrals ignore jumps.

## Review disposition and exact joint coverage

R-new-bracket holds on its original whole \(L\ge27\) with the correct cube and the re-anchored interval in the pointwise intersection. The historical R-old-alt-bracket has its original whole \(L\ge36.98\) with the cube replacing the invalid direct leaf, the historical \(h_1+m_1\) omitted, and the other eligible B0 leaves (including ES with strip \(1/8\)) and the upper sign through 43 kept. Its lower inputs are positive: the cube bound is decreasing and \(<1\) at 35.98; \(h_0+m_0<1\) from 40. No assertion is made that an intersection with an invalid leaf survives numerically at every point. The unmodified historical R-old-alt-bracket is not imported.

The code rechecks all original ROWS and RUNGS at the same parameters. This completes R-finite-profile-0 through -4, retains -5, and restores R-connected-plus8 from 47.7 (closed cells to 191 and an analytic tail). The split points include 58/59, 43.7/44.7, 29.9/30.9 and 185/186, with separate eligibility at each argument. For a negative term \(K e^{-u/2}(1-e^{(s-u)/2})/u\) in an upper cap, use a lower bound for \(e^{-b/2}/b\) and \(1-e^{(s-a)/2}\) on \([a,b]\). Positive errors use the decreasing parts at the left endpoint. The sign-sensitive square comparison is as in ramanujan_repair.md. EXTRA uses the same entire-cell inequalities; if a parent fails, replace it by both closed halves, and fail the check if it still fails at width \(1/4096\). Neither a grid of samples nor a favorable exit status without checks is the proof.

For EXTRA_TAILS retain all positive terms through \(C_{20}\). In the \(RL^2/x^2\) normalization, after subtracting the proposed profile multiply by \(L^{20}\). The retained positive terms, including \((C_j-z)L^{20-j}\), are nondecreasing. The negative square tail and the analytic losses, scaled by \(L^{20}\), decrease in magnitude from \(A\ge191\): freeze \(C^*(A-1)\), \(20/L<1/8\), an extra numerator \(u\) occurs only with the fast anchor exponential, \(V\)'s inverse-power term has exponent 21, and the remaining factors \(L/(L-1), H, V\) and the unscaled positive errors decrease. A strict check at \(A\) suffices.

## Improved real-ray and finite profiles

In units \(Y=L^6R/x^2\):
* Strict constant margins .04, .30, .70, 1 start at \(L=27.75,28.24,29.19,30.59\), respectively. At the previous onsets \(27.8,28.3,29.2,30.75\) the available margins are .06,.33,.715,1.03. The common tail uses \(Y>1+14/L+16/L^2\) from 191. On \([34.3,43.7]\) one has \(Y>1.405\).
* \(Y>1+14/L+z/L^2\) on rays from \(47.64,47.645,47.647\) with \(z=8,8.30,8.34\) respectively. Also \(z=10\) from 189.36, \(z=14\) from 189.9 and \(z=16\) from 191. Locally \(z=10\) on \([47.68,187]\), \(z=25\) on \([47.97,184]\), and retain the old +100 slab. The full quadratic plus \(1050/L^3\) is supported on \([56,105]\). There is no +10 connection through the remaining gap.
* Same full-polynomial rung strengths for \(j=7,8,9,10,12,15,16,19\) now from \(L=221,254,288,323,394,502,538,647\). Keep all other original rungs, and see ram_high.md for deeper profiles.

Take the applicable maximum of the lower margins and pointwise brackets. A +8.36 adaptive sufficient test still failed near 189.123, and an unfrozen density pointwise scout at the CH2-to-density switch also left a dip below +10. The high-L mixed endpoint cost, not the finite π correction, controls this bottleneck. Trying +105 on \([50.1,157]\) also failed the sufficient comparison, not the theorem. Conditional FKS \(a_1=.618\) numerics are not imported (Remark 1.5(2), PDF p.3). The exact optimal sign endpoint does not change; independence from DP Lemma 3.4 would need a further large finite verification, not required at admitted literature trust.
