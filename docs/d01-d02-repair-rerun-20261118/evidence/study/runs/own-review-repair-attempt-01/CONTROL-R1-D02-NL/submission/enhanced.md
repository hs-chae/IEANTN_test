# Mertens repair continuation: sharper rays and pointwise envelope

All of mertens.md, including the exact finite menu and signed source intersections, is retained. This supplement strengthens the supported branch, which did not use the disputed finite \(\pi\) estimate. No change of normalizers: \(E_S,E_W,Z,P,Q\) and their relative errors mean exactly what they mean there. The improvement to the tail integration in (2) below is valid even when the pointwise \(\psi\) information is not improved. Inclusive real domains, non-strict error bounds. The constants are declared in enhanced.py and checked with exact outward arithmetic.

## A sharper density integral and the finite-height saving

Use the notation \(p,q,a,h,D\) of common.md in this section only. From the same Dusart Theorem 2.3 and finite RH, replace \(D(s)\) by
\[
 D_4(s)=2\left[4.9\,3^p h^q e^{-ah}
   \sum_{j=0}^{4}\frac{q(q-1)\cdots(q-j+1)}{a^{j+1}h^j}
       +51.5\frac{h^2+2h+2}{H_0}\right]                  \tag{E1}
\]
with the empty falling factorial for \(j=0\). Indeed, \(3<q<4\) on the entire common strip \(s_0=.77\le s\le b\); the fifth derivative of \((1+w/h)^q\) is negative for \(w\ge0\). The fourth Taylor polynomial is an upper bound (with all coefficients positive). Integration against \(e^{-aw}\) gives (E1). This polynomial is also bounded from above by \(e^{qw/h}\) termwise: in the polynomial each falling factorial is at most \(q^j\). Thus \(D_4<D\), and \(D_4\) decreases with \(s\) since all \(q\)-products, the common numerator factor and the inverse powers of \(a\) decrease. Equality at the strip limit is not ruled out. (E1) can be used in the exact layer integral, or at left mesh endpoints. It is shared by B0 and B1; only \(b\) changes.

Let \(G_4(v)\) be the positive mesh mixture of common.md with \(D_4\) replacing \(D\), using step .000125 for the Mertens rays. On \(v\ge100\) reduce it further:
\[
 G_4^+(v)=G_4(v)-[55+D_4(s_0)]e^{-(1-s_0)v}.
\]
For \(40\le v<100\) set \(G_4^+=G_4\). The finite-height improvement follows from Platt–Trudgian 1809, Lemma 2, PDF p. 4: \(\sum_{0<\gamma\le H_0}1/\gamma>55\) by the lower leg of that lemma, checked in enhanced.py. In the truncated formula, the right-of-center reciprocal mass of **both** signs is at most the mass of the positive ordinates above \(H_0\) through \(T^*\), by reflection \(\beta\mapsto1-\beta\). If \(T^*\le H_0\) this mass is zero. Otherwise subtract the known lower bound 55 from the old \(1+v^2/48\) bound. For \(v\ge100\) the difference is positive, so it works also if \(T^*\le H_0\). This saves 55 at the base right-half-line weight. Save \(D_4(s_0)\) at the same weight by retaining the negative endpoint when telescoping the layer. The original both-sign estimate for the low/background contribution is left unchanged. The resulting total background coefficient for \(e^{-(1-s_0)v}\) is \(v^2/48-54-D_4(s_0)>0\) (use \(D_4(s_0)<116\)). This is not a subtraction from an already majorized integral with uncontrolled direction: both terms are reductions to the exact expression before upper-bounding the zero sum. The tighter mesh/density branch is no larger than the original fine branch, by the layer representation and positive increments. It shrinks strictly when the strip endpoint is moved from \(7/8\) to \(27/32\), by positivity of the excluded layer.

## Oscillatory kernel improvement and tails

Retain \(J_H\) of (2) in mertens.md. For \(J_A\) replace (2) by the smaller
\[
                     J_A^+(L)=K(L)J_H(L).
\]
For each nontrivial zero, \(K(v)=\int_0^\infty(1+t)e^{-tv}\,dt\) on \(v>0\). Apply Fubini to the individual integral from \(L>0\) to infinity (absolute convergence follows from \(\beta<1\)), and use \(|1+t-\rho|\ge|1-\rho|\) for \(t\ge0\). Its zero term is bounded by \(K(L)e^{(\beta-1)L}/|\rho(1-\rho)|\), with factor one rather than two. The compact \(L^2\) and infinite-limit proofs in mertens.md still justify the sum. This does not change the elementary contribution and does not depend on B1 except for the same off-line exponent.

Sharper tail bounds are obtained by replacing \(\epsilon(e^t)\) in the proof of \(U_1\) by any symmetric cap for \(|z(v)|\) valid **uniformly on \(v\ge t\)**. The implementation takes the minimum of the following admissible caps:
1. Dusart \(20.83/t^3\) on \(t\ge10/3\).
2. \(C(t)+\mathrm{POWER}(t)\), monotone for all such \(t\).
3. For \(4\log 10\le t\le29.933\) use the maximum of \(1.751000147e^{-t/2}+1.78e^{-2t/3}\) and \(C(29.933)+\mathrm{POWER}(29.933)\), to account for the expired finite CH2 lemma later in the integration. The implementation uses an upper rational bound for \(4\log10\).
4. For \(7\le t\le58\) take the maximum of \(t^2e^{-t/2}/25.1327412\) and \(C(58)+\mathrm{POWER}(58)\), where the first is the printed finite-\(\theta\) estimate, real \(e^t>599\).

All are caps for the full range of the relevant tail, not just pointwise estimates at its left endpoint. Their joined minimum is nonincreasing: the finite options enter by minimum, and at exit the cap is at least the value of the persistent branch 2, so removing it causes no upward jump. Write \(U_1^+\) for this strengthened tail. Its expression is nonincreasing in \(L\) and no larger than the original. The same \(\epsilon\) can strengthen each other use in mertens.md on its domain, including the lower/upper square and \(U_0\) estimates; use the true smaller cap only where a tail-uniform bound is required. The signed intersections can take either the new or the old interval. For \(L\ge24\) also apply the two-sided tuned CH2 grid of ramanujan.md directly to \(\delta\) (upper add the center shift). For symmetric tests cap the absolute value with both-sided radius plus the nonnegative maximum center shift. These are B0 improvements. In the new main oscillatory branch, replace the input by the intersection including \(G_4^+\) and use the smaller \(J_A^+\). It never worsens either side of the signed primary interval. It strictly improves both sides from \(L=170\) when replacing B0 by B1 in this branch (this follows from the old strict floor comparison checked in mertens.py, the positive excluded layer, and reduced \(J\)); the final minimum over all original and new envelopes is never worse but need not be strictly improved at every point by this reasoning alone.

## Whole-ray constants and proof of the finite joins

Use exactly the same bounds/normalizations as in the power menu in mertens.md: on a row \((b,u,c)\) the bounds are \(ce^{-\alpha L}\) for \(|E_W|\), and \(ce^{-\alpha L}/L\) for each of the other three errors, where \(\alpha=1/8\) in B0 and \(5/32\) in B1. Further rows are POWERS in enhanced.py. Among them (not exhaustive):
\[
\begin{array}{c|r|l}
 &u&c\\\hline
\mathrm{B0}&190&.01291\\
&219&.0115\\
&310&.0095\\
&800&.007565\\
&2000&.007024\\
&5000&.006831\\
\mathrm{B1}&175&.24845\\
&196&.222\\
&200&.21726\\
&288&.172\\
&300&.16872\\
&1000&.12878\\
&2000&.12259\\
&5000&.11918
\end{array}
\]
The former B1 .222 at 200 and .172 at 300 are therefore improved both at fixed onset and at fixed coefficient. The pointwise answer keeps the minimum, not one row globally.

On these powers use the older \(U_1\) for the analytic tail to simplify the monotonic proof. Scaling \(G_4^+\) by \(e^{\alpha L}\), each monomial in the positive part is nonincreasing on the tested rays. The subtracted-background polynomial has log derivative after scaling equal to \(2L/[L^2-48(54+D_4(s_0))]-(.23-\alpha)\); it too is decreasing and negative for the onsets (check the weaker rate with \(54+D_4(s_0)\) replaced by 170 at each onset, as in pc). The unscaled background is nonincreasing from 100 by the same check with \(\alpha=0\); the join at 100 drops, not rises. This proves the scaled radii for \(E_W,A,E_S,Z\) are nonincreasing, since \(K(L)L=1+1/L\) and all rescaled corrections in the older proof are decreasing. The product conversion \(p(1+2pe^{-\alpha L}/L)\) with scaled log-bound \(p\) is likewise controlled at the onset. Scaling elementary exponential terms *before* outward rounding avoids underflow-amplified intervals at high \(L\).

The new early power rows are **B0 \(c=.01318\) on real \(x\ge368359\)**, and **B1 \(c=.2612\) on \(L\ge10\)**. On \([40,V]\) use the separate scaled CH2 floor and square-root endpoint estimates as in mertens.md; the pivots \(V\) are 185.97 and 167.94. The test at \(V\) from pc covers thereafter, both joins included. On \([14,40]\) in B0 and \([10,40]\) in B1, finitepower evaluates bounds on every closed cell with log step .05 (add the split 29.933). At the left endpoint use positive decreasing unscaled radius and tail bounds; for multiplying by \(L\) or \(e^{\alpha L}\) use the right endpoint. \(24,40,100\) only add branches or reduce a bound, so cells ending at such cutoffs remain valid by the former branches. At a cell starting at 29.933 admitting a right-hand limit, take also the non-expiring branch minimum at that point. All exponents, logs and floors are outward checked. This proves the full finite intervals and not merely estimates at a grid of \(x\)'s. Finally in B0 the previous finite .40 menu applies to all four errors from 368359; the ratio needed to convert to the new power bounds is \(.4e^{L/8}/L^2\). It decreases until \(L=16\), and the interval evaluation at \(\log368359<14\) is strictly below .01318. This covers the remaining finite join with an explicit shared endpoint.

The additional pure-logarithmic rows NEWLOG have the convention of LOGS in mertens.md. The finite test is on closed cells in \([16,320]\) with log step .1 and a split at 29.933. Admit the right-hand limits at 29.933 and 58 for expiring inputs. Radial caps are decreasing between joins as proved above; \(\delta\) uses \(.791e^{-L/2}\) only for \(\log 10^4<L\le29.933\). The cell uses left radii and right powers. Computationally, specgrid evaluates exactly the same \(G_4^+\) at the grid values by updating each exponential with a rigorous constant-step interval multiplier; no interpolation or extrapolation is made based on measurements. The entire tail after 320 uses pc and the monotone scaled factors \(L^j e^{-\alpha L}\) for \(2\le j\le9\). For example at \(u=55,k=6\) the product/reciprocal-sum coefficient is \(43.526\) in B0 vs \(23.559\) in B1; at \(u=40,k=8\) it is \(1507417\) vs \(760494\); at \(u=200,k=6\), \(11.003\) vs \(.37409\). No implication across unequal exponents is inferred from constants alone.

## Continuous late bound

With the exact layer instead of the mesh, \(-D_4'/D_4<150\) on the entire common domain. The common numerator contributes \(\frac83(h+\log3)+2\log h\) to the magnitude of each logarithmic derivative. For the denominators the largest contribution is \((40/3)/a_{\min}\), \(a_{\min}=1-8(1-.77)/3\); for falling factorials it is at most \(2\sum_{j=0}^3(13/4-j)^{-1}\). Their sum is \(<150\) by the executable interval check. The bound passes to the positive sum in (E1), including the constant. Thus \(D_4(b-t)\le D_4(b)e^{150t}\). After scaling by \(e^{\alpha L}\) the layer contributes at most \(D_4(b)L/(L-150)\) for \(L>150\), extending the integral in \(t=b-s\) to infinity. For \(L\ge1000\) all other scaled terms, including the products' and sums' \(J\) terms and tails, are collectively bounded by \(1.01\cdot10^{-11}\) using the original backgrounds and checking the endpoint 1000. The bound on the scaled non-product terms is then decreasing after 1000. With the separate exponential conversion of the log-product bound, the following constants work for **every \(L\ge100000\)**: B0 \(c=.006750\); B1 \(c=.11826\). The proof and check use the true power exponents, not a fit. The limiting coefficient of this particular continuous majorant is at most \(D_4(b)+10^{-11}\). No exponent above \(5/32\) or optimization of the actual error is claimed.

## Matched comparison

Keep everything in the original signed comparison and take the minima with this supplement. The matched simple powers have their exact cross-mode comparison \(e^{L/32}>c_1/c_0\), when both apply. For the **two exhibited early rows** this gives the unique crossing \(32\log(.2612/.01318)\) on the common domain; the earlier B1 branch has no strict advantage over the stronger B0 minima there merely by having a larger exponent. From \(L\ge140\), the B1 .34621 row beats every B0 row of the two displayed simple exponential menus (even against the smallest B0 coefficient .006750 extrapolated back only for the comparison, not as a bound); the strict 140 test is in enhanced.py, and the ratio decreases. For log-power and original-source comparisons use the ratios and domains in mertens.md; this never drops a stronger original input. In particular the pure-log/pointwise branches can win earlier than the simple power rows. This is a within-method ablation, not an independently blind baseline and not a claim to exhaust possible deductions from the original packet. The common-source cutoffs, power-tail limits, finite joins and direct error conversions do not need D02; the B1 improvements in the spectral and oscillatory branches use exactly the narrower strip obtained from it.


### Rate bottleneck is also an inverse implication

If for some \(0<\alpha<1/2\) the centered weighted error satisfies \(E_W(x)=O(x^{-\alpha})\), then Stieltjes partial summation with weight \(t\) gives
\[
 \theta(x)-x=xE_W(x)-\int_{x_0}^x E_W(t)\,dt+O(1)=O(x^{1-\alpha}).
\]
For \(E_S(x)=O(x^{-\alpha}/L)\), the same argument with \(t\log t\) (the main derivative of \(\log\log t\) gives \(dt\)) yields
\[
 \theta(x)-x=x\log x\,E_S(x)-\int_{x_0}^x (\log t+1)E_S(t)\,dt+O(1)
             =O(x^{1-\alpha}).
\]
Either relative product bound of the same rate gives the latter \(E_S\) estimate by taking a logarithm for large \(x\) and using \(E_S=Z+U_0\). Prime-power correction makes \(\psi(x)-x=O(x^{1-\alpha})\), and the integral continuation argument in common.md then excludes zeros with \(\Re\rho>1-\alpha\). Thus improving the power (with the stated log factors) for any of these four quantities would itself imply a stronger zero-free half-plane. This does not rule out proving one under the given premises; it explains why tighter real joins, density constants, and better oscillatory tail integration alone do not supply a proved larger exponent.
