# Mertens and prime sums: new post-review envelopes (B0)

Use the inclusive real definitions in candidate.md and mertens_repair.md. The validated earlier floors and signed intervals remain available. The assumptions are the same seven originals; the new direct-ψ premise is redundant. The claimed improvements are over named previous B0 recipes on matched real domains, not over all possible B0 derivations.

## Finite steps and entire analytic continuations

Every row below asserts both normalized relative product errors and \(|D_1|\) at most \(K/L^3\) on its entire subsequent **closed** real ray.

| x onset | K | certified finite top | sufficient analytic log onset |
|---:|---:|---:|---:|
|3909275995|.011|9000000000|22.9|
|38622120594|.004|90000000000|25.2|
|103268901665|.003|170000000000|25.83|
|149179986112|.0024|290000000000|26.35|

The first improves the previous .011 start 3909288921, and the other three lower the step constants before the inherited .00205 ray from \(L=27\). The finite claims use exactly the successful **terminal suffixes** of the m_coarse.cpp checks, not their larger input ranges. Before-suffix failures do not prove counterexamples. The .004 full interval from 50000000000 also separately passed with zero failures. See POST_REVIEW.md and postreview.log for the actual commands and results. This is the earlier whole-cell algorithm, with 64-bit stored prime values, within its explicit \(3\cdot10^{11}\) guard. Dusart 5.6, \(M<1\), and prefix monotonicity give a common prefix upper bound 5 in units \(2^{60}\) throughout the checks; the counts fit and the written fixed-point intermediate products fit 128 bits. Prefix enclosures and opposite endpoints cover every prime jump. The .999 radius reserve pays for both relative-product conversions, as proved in mertens_repair.md. m_postreview.py verifies that each finite top strictly exceeds its analytic onset; the analytic rays are proved below.

## Signed transfer on the moderate slab

Write \(s=e^{-L/2},t=e^{-2L/3},r=e^{-L/8},X=e^{-L}\), \(w(v)=(v+1)/v^2\), \(k=1+1/L\), \(q_w=(L+2)/(L(L+1))\). Let \(P(v)=e^{-v}(\psi-\theta)(e^v)\) for this calculation. On the closed slab \(29.9\le L\le43.7\), with \(m=\Delta-d_\theta\), the exact identities give
\[
LD_1=\Delta-m-L\int_L^\infty d_\psi(v)w(v)dv+L\int_L^\infty P(v)w(v)dv,\quad
D_2=\Delta-m-\int_L^\infty d_\psi(v)dv+\int_L^\infty P(v)dv.
\]
For \(LZ_Q\) subtract \(LT\) from the first line, with \(0\le LT\le.502X\) by mertens_repair.md. Use the \(s_{\rm anchor}=18\) bound \(-D_{18}-2.81s/L\le m\le D_{18}\) from finite_anchor.md. In both scaled identities, the absolute ψ integral is at most \(k(.048s+3.3\cdot10^{-12}r+2X)\) by the primitive and weighted bound in mertens_repair.md and d01_smooth.md. The prime-power integral is between \(.9999(2-4q_w)s\) and \(k(2.0000003s+2.67t)\): use the convex tangent lower estimate and decreasing weight for the upper, as in d01_smooth.md, or weight 1 for \(D_2\).

It follows that \(LD_1-\Delta,\ D_2-\Delta,\ LZ_Q-\Delta\) are between 0 and \(2.25s\). For the lower bound subtract \(D_{18}\), the absolute integral, and \(.502X\) from the lower prime-power integral. For the upper bound add \(D_{18}+2.81s/L\), the absolute integral and the upper prime-power integral (the nonnegative \(LT\) need not be added). Divide by \(s\): bound decreasing terms \(1/L,\ L e^{9-L/2},e^{-L/6},e^{-L/2},q_w\) by their values at 29.9 and the increasing \(e^{3L/8}\) by its value at 43.7. Both comparisons are checked in pi_constants(). The PT finite π bounds and finite-RH §3.3 sign, with normalization allowances as in ramanujan_repair.md, yield \(-2.25s\le\Delta\le0\) throughout that slab. Thus the maximum of \(|LD_1|,|D_2|,|LZ_Q|\) is \(\le2.25s\), by opposing signs rather than adding absolute radii. The signed interval with the pointwise bounds can be retained before exponentiation.

On \(18\le L\le29.9\) keep the sharper \(|D_1|,|Z_Q|\le u(L)\) of m_repair.py. For the weighted output on this slab, also use
\[
 |D_2|\le1.837401s+2.67t+3.2\cdot10^{-12}r+2X .
\]
Indeed \(D_2=d_\psi(L)-U(L)+s-\xi(L)+\int_L^\infty\xi\) with \(P(v)=e^{-v/2}+\xi(v)\), \(-.0001e^{-v/2}\le\xi(v)\le .000000147e^{-v/2}+1.78e^{-2v/3}\). The CH2 endpoint \(.791s\), \(|U|\), and upper \(\xi\) integral give \(1+.791+.0463+.0001+2\cdot.000000147<1.837401\). The lower direction drops the nonnegative leading bias and uses \(.751s\) and the reverse excess bounds, dominated termwise. The \(L^2\)-scaled right side decreases on this slab.

## Common envelope using the signed prime-power bias

For \(L\ge18\) let \(\Psi(L)\) be any valid absolute ψ relative cap. Let \(Z=3.3\cdot10^{-12}\) before 190 and \(Z=4.5\cdot10^{-15}\) after and including 190. The latter follows from \(G(190)/H<4.49\cdot10^{-15}\) in d01_smooth.md §2, the decreasing \(G\), and the factor \(1+2q_w/H\). Then
\[
\max(L|D_1|,\,L|Z_Q|,\,|D_2|)\le E(L)
=\Psi(L)+(1+.0003+.048k)s+k(2.67t+Zr+2X)+.502X.
\]
In fact subtract the pure square-root component of \(P\) before bounding errors. Its signed bias is \(s\) for \(D_2\), and \(LB_1\in[0,s]\) for \(LD_1\) by the identity for \(B_1\) in mertens_repair.md. The two directions of the remaining \(\xi\) costs are bounded by \(.0003s+2.67k t\), since their sqrt charges are \(.0001+2k\cdot.000000147\) and \(.000000147+2k\cdot.0001\), and their cube charges are \(1.5k\cdot1.78\) and \(1.78\). Use \(k\le19/18\). Add the ψ integrated bounds and product correction above. This pays the main bias only once and gives the correct log-to-relative product radius \((E/L)/(1-E/L)\) when \(E/L<1\) (or intersect signed intervals first).

For \(43.7\le L\le58\), use the minimum of CH2's \(\Psi=q+113.67s\) and \(cL^2s\), now sourced from the **ψ** line of finite RH Cor.1. For 58 to 190 keep the CH2 branch. In bounded slab tests \(qL^2\) is bounded at the right endpoint, with every other scaled \(L^2\) term decreasing there, including \(L^4s\) in the finite ψ leaf. Beyond 190 use \(F^*(L)e^{-L/8}\), and this latter power branch can also be used back to 185. In the units \(x^{-1/8}/L\) for \(D_1,Z_Q\) and \(x^{-1/8}\) for \(D_2\), its coefficient is
\[
 U_*=F^*(L)+(1+.0003+.048k)e^{-3L/8}
          +k(2.67e^{-13L/24}+Z+2e^{-7L/8})+.502e^{-7L/8}.
\]
The relative product coefficients are bounded by \(U_*/(1-U_*x^{-1/8}/L)\) in units \(x^{-1/8}/L\). Both coefficients decrease on the entire real ray \(L\ge185\), including the downward \(Z\) switch; their denominators are positive once verified at the onset. Relative to the old common refined power radius in mertens_repair.md, the new function is strictly smaller throughout \(L\ge185\) (compare the positive powers termwise, using \(C^*-F^*\), the old integral coefficients and \(L e^{-7L/8}\)). Other valid signed and pointwise bounds can still improve on both. Certified common coefficient/onset pairs include:

| L onset | power coefficient | L onset | power coefficient |
|---:|---:|---:|---:|
|185|.01973|187|.01955|
|190|.01929|250|.01612|
|400|.01345|600|.01230|
|900|.01163|1300|.01125|
|2000|.01097|3500|.01076|
|9000|.01058|12000|.01055|
|18000|.01051|100000|.01047|

On the extended density mesh, \(.874991,\ldots,.874999\) in steps of \(10^{-6}\) and \(.8749991,\ldots,.8749999\) in steps of \(10^{-7}\) are appended to the previous final point \(.87499\). Use the same FKS Cor.2.9/Table 8 [.87,.88] constants, integrated quartic enclosure and monotone running minima (density_refine.md). Appending points replaces some terminal-band weight, formerly charged with exponential factor 1, by nonnegative band weights with smaller factors. Thus the fine pointwise coefficient never worsens the previous one; it is still decreasing, and is available in \(U_*\). It yields \(.010456,.010451,.010447,.010446,.0104448\) from \(L=100000,200000,500000,1000000,5000000\), respectively, in the same units for all four outputs. No claim is made that this is a smallest possible positive limit or that a zero attains the closed strip boundary.

The functions are the stated mathematical real functions, not their rounded implementations at untested arguments. Every polynomial-log comparison closes beyond 190 since \(L^2e^{-L/8}\) decreases there; beyond that point the power coefficient also decreases.

## Logarithmic rays and weighted step transfer

These closed real rays use units \(L^{-3}\) for products and \(D_1\) and \(L^{-2}\) for \(D_2\).

| L onset | products/D1 | D2 |
|---:|---:|---:|
|27|.00205 (inherited)|.002|
|28.39|.001|.00111|
|28.5|.001|.001|
|29.35|.00066|.000734|
|29.45|.00066|.00066|
|30.68|.00050|.00050|
|32.3|.00025|.00025|
|34.4|.00010|.00010|
|36|.00005|.00005|
|46.1|.00002|.00002|
|49.56|.000005|.000005|
|49.97|4.4e-6|4.4e-6|
|59.95|8.2e-8|8.2e-8|
|64.4|4.3e-8|4.3e-8|
|74|3.8e-8|3.8e-8|

Thus for products/D1, .001 starts at 28.39 instead of 32; 8.2e-8 for all four starts at 59.95 instead of 60. Proof of joins: test the proper early decreasing scaled radius where needed, then \(2.25L^2s\) decreasing across the signed π slab, then the split at 58 and 190 just described. The code may convert a scaled log cap \(v<1\) to a scaled relative cap \(v/(1-v)\) using \(v/L^3\le v\). The 64 trial of 4.3e-8 failed the particular uniform check, as did the 38.1 trial of .00002 at the 43.7 join and the .01606 power trial at 250; the listed corrections pass.

Retain the pointwise transfer using the **entire** later \(D_1\) step envelope. From the Stieltjes identity in mertens_repair.md, for decreasing step constants \(K_i\) on \([L_i,L_{i+1})\),
\[
L^2|D_2|\le1.5K_i-\tfrac12L^2\sum_{h>i}(K_{h-1}-K_h)/L_h^2.
\]
This follows by exact integration of \(v^{-3}\) and is decreasing in each step. For a whole ray take the maximum of the left endpoint bounds from that step onward using directed logs. With the finite steps above and the later analytic D1 steps, the weighted coefficients at
\(3909275995,4760000000,8500000000,12000000000,16000000000,22000000000,30000000000,38622120594,103268901665,149179986112\)
are respectively
\(.01212,.01104,.00983,.00872,.00763,.00656,.00549,.00445,.00332,.00269\).
Other step calculations are in m_postreview.py; the .00111 and .000734 table entries use this transfer. Never extend the transfer below its D1 domain to match an earlier product threshold.

Take the minimum of the new, old valid, and published eligible envelopes. No unconditional sign on an infinite ray or globally optimal Mertens coefficient follows. No improvement in power exponent or asymptotic logarithmic factor is claimed here: the local endpoint \(F^*\) (not the much smaller integrated term) controls the non-recentered errors. Increasing interval resolution improves some finite suffixes but does not prove earlier cells. Distinct outputs of the common derivations are correlated.
