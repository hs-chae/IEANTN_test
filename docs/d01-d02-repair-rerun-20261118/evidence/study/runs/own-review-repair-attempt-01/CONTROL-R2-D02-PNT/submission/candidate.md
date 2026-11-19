# Explicit Ramanujan and Mertens bounds under FOLLOWUP-D02

## 1. Statements, assumptions and comparison convention

Write \(L=\log x\), \(R(x)=e x\pi(x/e)/L-\pi(x)^2\), and \(G(x)=L^6R(x)/x^2\). All the domains below are **real** and include the stated starting point unless a strict endpoint is specified. \(B_0\) means the original packet, in particular OpenAIQRH Theorem 1.1. \(B_1\) means \(B_0\) plus the exact D02 majorant \( |\psi(x)-x|\le x^{27/32}(\log x)^2/64\) for every real \(x\ge e^{200}\). No full RH assumption is used. **The new companion `repair.md` gives stronger, active branches in both families, an earlier matched pointwise comparison, and the complete repair ledger.** The displayed certificates are ordinary exact-integer or outward-interval computations, not a formalization or source-first PV.

### Ramanujan

Under \(B_0\) the connected strict-sign ray is **\(x>r\)**, where
\[
  38358837682.21792636 < r < 38358837682.21792637.
\]
Here \(R(r)=0\) and (R) is negative immediately to the left. In particular \(r\) is the largest real counterexample to the *strict* inequality and 38358837682 the largest integer one. This correction/connection is input-independent; D02 does not improve this endpoint. See §4 for the exact equation defining \(r\) and the inherited finite computation used in the join.

Put
\[
 P_n(L)=\sum_{j=0}^n c_{j+4}L^{-j},\qquad
 c_k=\sum_{h=0}^k h!\binom{k}{h}-\sum_{h=0}^k h!(k-h)!.
\]
Thus \(P_0=1, P_1=1+14/L, P_2=P_1+145/L^2, P_3=P_2+1412/L^3, P_4=P_3+13985/L^4\); the next four coefficients are (145450,1610021,19063832,241691425). The following are **strict** lower bounds for \(G\).

|Profile|Sufficient log onset, \(B_0\)|Sufficient log onset, \(B_1\)|
|---|---:|---:|
|0.1|37|37|
|0.5|40.5|40.5|
|0.9|42.15|42.15|
|1|42.8|42.8|
|\(P_1+14/L^2\)|47.5|47.5|
|\(P_1+19/L^2\)|48|48|
|\(P_1+39/L^2\)|not certified at 48 by matched \(B_0\)|48|
|\(P_1+80/L^2\)|not certified at 53 by matched \(B_0\)|53|
|\(P_2\)|217|186|
|\(P_3\)|252|210.2|
|\(P_4\)|287|236|
|\(P_5\)|322|262|
|\(P_6\)|357|288|
|\(P_7\)|394|318|
|\(P_8\)|427|342|
|\(P_9\)|462|369|
|\(P_{10}\)|499|396|
|\(P_{12}\)|571|450|
|\(P_{15}\)|680|531|
|\(P_{20}\)|863|668|

The entries are sufficient onsets, not assertions of smallest onsets for a profile. At the *same* onset \(L=200\) the certified lower profile improves from \(P_1+115/L^2\) to \(P_2+1200/L^3\); at \(L=240\), from \(P_2+1300/L^3\) to \(P_4+60000/L^5\). These improvements are pointwise on the rays (compare coefficients). Keep the stronger bounded branches \(P_2\) on \([53,125]\), \(P_3\) on \([58,91]\), and \(P_4\) on \([65,71]\), already under \(B_0\). Take the maximum of applicable profiles, as well as the explicit non-polynomial lower bound (R) below and the strict sign branch. In particular a late higher-order onset is not a gap in the positive ray. Original PT 2021 Theorem 2 provides sign, not these positive margins; Dudek–Platt Theorem 1.2 supplies the older unconditional tail \(L\ge9658\), and PT 2021 supplies \(L\ge3915\). The relevant stronger comparator for *incremental* effects is our QRH-aware same-method \(B_0\), not those old tails.

### Mertens

Set \(\mathcal P=e^\gamma L P_{\rm raw}\), \(\mathcal Q=e^{-\gamma}Q_{\rm raw}/L\),
\[
 E_1=\sum_{p\le x}1/p-\log L-M,\qquad
 E_w=\sum_{p\le x}\log(p)/p-L+B_3.
\]
The exact constants are \(M=\gamma+\sum_p(\log(1-1/p)+1/p)\) and \(B_3=\gamma+\sum_p\log p/[p(p-1)]\) (Dusart Theorems 5.6–5.7). For each row with exponent \(a\), all of \(|\mathcal P-1|,|\mathcal Q-1|,|E_1|\) are **at most** \(C x^{-a}/L\), and \(|E_w|\) is **at most** \(C x^{-a}\), on \(L\ge L_0\).

| \(B_0: a=1/8\) | (C) | \(B_1: a=5/32\) | (C) |
|---:|---:|---:|---:|
|180|.025|160|.431|
|190|.0161|170|.302|
|200|.0135|180|.258|
|210|.0126|185|.247|
|220|.012|190|.238|
|250|.0111|200|.226|
|300|.0101|210|.217|
|400|.0091|220|.210|
|600|.0082|250|.193|
|1000|.0076|300|.176|
|2000|.0072|400|.159|
|4000|.0070|600|.144|
|10000|.0069|1000|.132|
| | |2000|.125|
| | |4000|.122|
| | |10000|.120|

The continuous-coefficient formula in §5 is stronger than rounding these tables, and the signed pointwise interval formula in §6 can be still stronger. At the common onset 200 the ratio of the \(B_1\) to \(B_0\) displayed power radii is \((.226/.0135)\exp(-L/32)<.033\), decreasing thereafter. Against the enumerated pointwise original-input envelope (including the \(B_0\) signed and ordinary spectral transfers), the D02 bound is strictly smaller throughout \(L\ge200\); see the guard proof in §6. More generally, between any two displayed power rows of different exponent the crossover is exactly \(L=32\log(C_1/C_0)\) if it is in the matched domain; do not compare where a branch is inapplicable. For example, a target radius of \(10^{-14}\) for \(L|\mathcal P-1|,L|\mathcal Q-1|,L|E_1|,|E_w|\) is certified from \(L=224\) by a displayed \(B_0\) row and from \(L=198\) by a \(B_1\) row. For target \(10^{-18}\) the respective choices are 296 and 255. These examples give sufficient onsets, not lower bounds on other possible methods.

**Input-independent finite/analytic joins.** Besides all original branches, the three unweighted errors have each of the following bounds, for all real \(x\) beyond the indicated **\(x\)** (not log) onset. Rounded onsets shared by the three outputs deliberately take the maximum of their separate onsets:

|radius|sufficient \(x\) onset|
|---|---:|
|.19/\(L^3\)|3451829|
|.18/\(L^3\)|3458977|
|.16/\(L^3\)|3474931|
|.15/\(L^3\)|5001809|

Additional analytic rays are \(.08/L^3\) on \(L\ge18.15\) and \(.04/L^3\) on \(L\ge20\) for all three unweighted errors. For \(|E_w|\): \(.27/L^2\) from 1513777, \(.24/L^2\) from 1526467, \(.21/L^2\) from 3446081, \(.18/L^2\) from 3470287, \(.079/L^2\) on \(L\ge18\), and \(.04/L^2\) on \(L\ge20\). Keep the direct Dusart .2/\(L^3\) at 2278382 for products and 2278383 for the reciprocal sum and .3/\(L^2\) at 912560 for the weighted sum. The witnesses in `finite-evidence.txt` certify why tighter uniform coefficients cannot just be asserted at those older onsets. The absolute-error envelope uses the minimum of **all** applicable branches, not a rule to discard stronger old estimates. A finite-range bound is not evidence that D02 changes those small-\(x\) oscillations.

## 2. Premise ledger and a spectral transfer used in both families

**Source locators (original PDF page numbers).** QRH Theorem 1.1, p.4, gives \(\zeta\) zero-free for \(\Re s>7/8\), not on the boundary. FiniteRH Theorem 1 p.2 gives verified height \(3000175332800\); Corollary 1 p.4 states the real \(\psi,\theta,\pi\) estimates on the finite ranges (the (\theta) range starts strictly at 599). CH2 Corollaries 1.2–1.3 p.3 and proof \(9.2\) p.36 give the finite-height estimates, and Lemma 9.2 p.35 and its proof give the small-input computations including the **scaled** weighted error. CH2 \(10.3\) p.38 is another independent \(\psi\) branch. Dusart p.5 Theorem 2.3 is the explicit Ramaré zero-density inequality; Theorem 4.2 p.11 and Corollary 4.5 p.13 give Chebyshev and prime-power bounds. The fact \(\theta(t)<t\) for \(1<t<1.39\cdot10^{17}\) used below is cited as a computation in the proof of that corollary. Dusart Theorem 3.3 pp.7–8 and Proposition 3.2/Table 1 pp.7–9, Theorem 5.1 p.14, Corollary 5.2 p.15, Theorems 5.6–5.9 pp.17–20 supply the other direct bounds. PT 2021 Lemma 2 p.4 supplies the reciprocal zero sum, Theorem 1/Corollaries 1–2 and Table 1 pp.2–3 the direct estimates, and Theorem 2 p.3 and \(18\) p.10 the Ramanujan comparisons. FKS pp.2–3 Theorems 1.1–1.2/Corollary 1.4 and Lemma 5.2 p.17 plus Tables 5–6 pp.22–23 supply comparison curves; its **Theorem 3.2** \(3.2\) p.8 for real \(x\) is the signed explicit formula used here. FKS Corollary 2.9 \(2.17\) pp.7–8 and Table 8 p.26, **first panel \(a_1=.77\)**, provide an alternative density bound; no use is made of the conditional improved subconvexity column. Dudek–Platt p.2 Theorems 1.2–1.3; pp.8–10 §3.1 and Lemma 3.4 supply the inherited finite sign evidence at the integer inputs in §4. The source receipt binds all seven TXT/PDF pairs. Recited computations remain literature trust, not new verifications of them.

### Zero exclusion from exactly D02

For \(\Re s>1\), by unique factorization, logarithmic differentiation of the absolutely convergent Euler product and partial summation,
\[
 -\zeta'(s)/\zeta(s)=\frac{s}{s-1}
   +s\int_1^\infty (\psi(t)-t)t^{-s-1}\,dt .
\]
D02 gives locally uniform absolute convergence and holomorphy of the integral on \(\Re s>27/32\): the finite part ending at \(e^{200}\) is entire and the tail is bounded on compacta by integrals of \(t^{-1-\epsilon}\log^2t/64\). Uniqueness of meromorphic continuation excludes a zero there (a zero of multiplicity (m) gives a nonremovable pole with residue (-m)). There is no assertion about the boundary. This inference uses the exact exponent, while the coefficient and onset ensure integrability and need not occur in the new density constants. This is the reason a conditional improvement need not wait for \(x=e^{200}\). The direct pointwise error bound itself is used **only** on its stated domain. Set \(\beta=7/8\) or \(27/32\) according to the premise and \(a=1-\beta\). Nontrivial zeros are paired by conjugation and reflection in \(\Re s=1/2\); no real zero in \(0<s<1\) (the alternating \(\zeta\) series there has positive sum and (1-2^{1-s}\ne0)).

### Cumulative reciprocal zero bounds

Let \(H=3\cdot10^{12}\), \(h=\log H\). All zeros with \(0<\gamma\le H\) lie on the critical line. For \(s\ge .745\), put \(p=8(1-s)/3, d=1-p, q=5-2s\). Here \(3<q<4\) for every band used. For \(Y\ge H\), the two applicable inequalities for \(N(s,Y)\) (positive ordinates, \(\Re\rho\ge s\), multiplicities) are \(A\,Y^p(\log Y)^q+B(\log Y)^2\), with
\[
 (A,B)=\big(4.9\,3^p, 51.5\big)\quad\text{or}\quad(c(s),5).
\]
The first is \(\log(1+z)\le z\) in Dusart 2.3; the second uses FKS Corollary 2.9. In increasing bands beginning at (.700,.750,.800,.810,.820,.830,.840,.850,.860,.870) take \(c(s)=6.1727,7.7979,8.2,8.6,9,9.4,9.8,10.2,10.7,11.1\), respectively, up to the next left endpoint (outward enlargements). At a shared endpoint the next band's bound is valid. These are cited as the *conclusion* of Corollary 2.9, not a recomputation of Theorem 2.7's optimization parameters. In particular there is a notation discrepancy involving the printed \(\delta\) range versus Table 8; the independent Dusart density can be selected by the `RAM_ONLY=1` replay. We do not use PT 2021's truncated formula \(7\) or FKS 3.1/Prop. 3.4 in the new proofs; FKS Remark 3.3 flags issues in the older truncated formulas.

For \(s\ge.745\), \(2\sum_{\Re\rho\ge s, \gamma\ge V}1/\gamma\), for \(V\ge H\) or \(V\) below \(H\) if the stated density bound is valid from \(V\), is bounded by \(2\int_V^\infty \widetilde N(s,y)y^{-2}dy\) using integration by parts, with no subtraction needed at the lower end. In uses with \(V<H\) below, simply use that the count is zero until \(H\), so the bound by a positive analytic majorant integrated from \(V\) is still valid. Counting \(\gamma=V\) is allowed. For \(V=H\) take the minimum of the two resulting upper bounds. With \(h=\log H\) one can majorize the integral of \(y^p(\log y)^q/y^2\) by
\[
 J_q = e^{-dh}h^q\sum_{j=0}^4 (q)_j/(h^j d^{j+1}).
\]
Indeed the degree-four Taylor polynomial of \((1+v)^q\) at zero is an upper bound for \(v\ge0\) (fifth derivative negative). The integral of \((\log y)^2/y^2\) is \((h^2+2h+2)/H\). Define \(C(s)=2\min(AJ_q+B(h^2+2h+2)/H)\) over the two densities. These constants need not be monotone as formulas across band edges; replacing each by the running minimum as \(s\) increases preserves the inequality.

For the mesh \(s_0=.745<s_1<\cdots<s_m=\beta\), take steps .001 up to the last endpoint (truncate the last step if necessary). Let \(C_i\) be the running minima through \(i\) for \(0\le i<m\), and set \(C_m=0\) **only as a notation for telescoping**, not a bound on the zeros at \(\beta\). Define
\[
 Z_\beta(u)=\sum_{i=0}^{m-1}(C_i-C_{i+1})e^{-(1-s_{i+1})u}.
 \tag{Z}
\]
This bounds the absolute contribution of all high zeros \(\Re\rho\ge s_0\) to the relative explicit formula at \(e^u\). In fact each exponential \(e^{-(1-\Re\rho)u}\) is bounded by its right mesh endpoint plus the usual cumulative-level telescoping, including a zero precisely on the cap. This argument gives the alternative expression \(C_0 e^{-(1-s_0)u}+\sum_i C_i(e^{-(1-s_{i+1})u}-e^{-(1-s_i)u})\); from it reducing the cap decreases the bound. All positive sums are absolutely convergent.

### Relative Chebyshev error

For \(u\ge60\) use FKS \(3.2\) with \(x=e^u, T=e^{u/2}/6\), so \(T\le T^\star<e^{u/2}\) and the relative remainder is \(12.546 u e^{-u/2}\). This meets \(T<(e^{u/2}-2)/5\), \(T>\max(51,u)\), and the onset \(u\ge40\). Write
\[
 S=(u/2-1.83)^2/12.56+.933,\qquad
 J=((u/2-1.83)^2-26.88^2)/12.56+1.865,\qquad
 U=(12.546 u+2S)e^{-u/2}.
\]
By PT Lemma 2, \(S\) bounds the reciprocal sum over positive ordinates up to \(e^{u/2}\); \(J\) bounds it above \(H\). Use \(1.83<\log(2\pi)<1.84, \log H>28.72\). Conjugate zeros double the weight; the reflected zeros left of the line cost at most the line contribution. Off-line zeros on the right above height \(H\) consume at most half the reciprocal sum above \(H\) by reflection. Writing their excess via the mesh gives
\[
 |\psi(e^u)/e^u-1| \le b_\beta(u)
 = U+ (J-C_0)_+e^{-(1-s_0)u}+Z_\beta(u).
 \tag{B}
\]
Only the two caps are compared here. In particular both yield a decaying error with the corresponding power and no positive log factor. We also have all original applicable envelopes and, under \(B_1\), the direct \(u^2e^{-5u/32}/64\) at \(u\ge200\). For \(\theta\), add the prime-power relative bound
\[
 D_+(u)=1.000000147e^{-u/2}+1.78e^{-2u/3}
\]
from Dusart 4.5, and intersect with all direct \(\theta\) bounds. One may use the tighter signed interval \([-b-D_+, b-D_-]\), with \(0\le D_-\le(\psi-\theta)/x\) as in §5. These transformations never decrease the established domains. Below 60 no explicit-formula claim is made by (B).

## 3. General lower profile and proof of the real-ray certificates

Define \(I_2(x)=\int_2^x dt/\log t\). The normalization is deliberate. Partial summation gives
\[
 \pi(x)-I_2(x)=\frac{\theta(x)-x}{L}
   +\int_2^x\frac{\theta(t)-t}{t\log^2t}\,dt+\frac{2}{\log 2}.
\]
If \(B_\theta(u)\) is a bound for \(|\theta(e^u)/e^u-1|\), the dimensionless error for \(\pi/(x/L)\) is bounded by
\[
 b_\pi(L)=B_\theta(L)+Le^{-L}\left[2/\log2+
                 \int_{\log2}^L e^u B_\theta(u)\,du/u^2\right].
\]
The proof uses the minimum of relevant enclosures. Details of the enclosure used in `verify.py` follow, so no quadrature assumption is needed.

* CH2 Corollary 1.3 gives \(c+113.67e^{-u/2}\) for \(\psi\), with \(c=1.0472\cdot10^{-12}\); thus \(c+117e^{-u/2}\) bounds \(\theta\) for (u\ge\log 2). A second branch for \(u\ge34\) uses CH2 Corollary 1.2 at \(T=\min(e^{u/2}/2,3000175332800)\): if \(v=\log(T/(2\pi))\), its \(\psi\) radius is \(\pi/(T-1)+\pi^2/(3T^2)+(v^2/(2\pi)-v/(6\pi))e^{-u/2}\). Here \(x>\max(T,10^9),T\ge10^7\), and \(1/y\le\coth y\le1/y+y/3\) as in CH2 \(9.2\). Add \(D_+\).
* FiniteRH Corollary 1 gives \(.04u^2e^{-u/2}\) on \(6.4<u\le58.33\) \((e^{6.4}>599, e^{58.33}<2.169\cdot10^{25})\). For a prefix ending at \(e^v\) in this range the integral and normalizing constant together cost at most \(.08L e^{v/2-L}+1255Le^{-L}\). Use \(|\theta(t)-t|\le t\) for \(2\le t\le599\) (Dusart 4.2), and then the finite RH estimate itself on \(599<t\le e^v\). In particular the first line of `early` is this with \(v=L\).
* For a general prefix ending at \(e^v\), use \(c+117e^{-u/2}\). Split at \(u=v/2\) and use
\[
 \int_{\log2}^{v} e^{ku}du/u^2
 \le 4e^{kv}/(kv^2)+1.45e^{kv/2},\qquad k=1,1/2
\]
on the domains used. Multiply by \(Le^{-L}\) and add \(3Le^{-L}\) for the normalization.
* In the last 8 log units (if the finite RH branch holds throughout at the top) or last 16 units otherwise, divide into unit cells \(u=L-z, z\in[j,j+1]\). Multiply the interval bound for \(B_\theta(L-z)\) by \(L(e^{-j}-e^{-j-1})/(L-j-1)^2\). Use the minimum of the global, finite-height, (B), and direct-D02 radii that hold on that **whole** cell. For the upper \(\pi\) error only, if \(L\le39.47\), use also \(3Le^{-L}\) by \(\theta(t)<t\) (including \(\theta(2)\le2\)), since \(e^{39.47}<1.39\cdot10^{17}\). The lower error is not replaced by this one-sided bound.
* Analytic tail: for \(u\ge60\) majorize \(B_\theta(u)\) by
\[
 b^*(u)=(.04u^2+13u+2)e^{-u/2}+D_+(u)+.02u^2 e^{-.255u}+Z_\beta(u).
\]
Here \(U\) and \(J\) have the asserted polynomial majors by expansion. For \(L\ge120\), use this for the integral with \(u\ge L/2\), the general prefix up to \(v=L/2\), and the same \(b^*\) for the endpoint. For any term \(c u^j e^{-du}\), \(0<d\le2/3, j\ge0\), the late integral costs at most \((12/L)c L^j e^{-dL}\), since \(u^j\le L^j, u^{-2}\le4/L^2\) and \(\int_0^\infty e^{-(1-d)z}dz\le3\). This gives `tail_pi_end`, which can be intersected with the unit-cell rule without worsening it.

For \(m=12\) let \(A_m(L)=\sum_{j=0}^m j!/L^j\). Integrate by parts from \(y=e^{10}\):
\[
 I_2(x)= (x/L) A_m(L) - K+(m+1)!\int_y^x dt/\log^{m+2}t,\quad
 K=(y/10)A_m(10)-I_2(y).
\]
\(|K|<2500\) follows by bounding \(I_2(y)\) below by \((y-2)/10\) and above by \(y/5+e^5/\log 2\), checked in `aux`. The upper remainder divided by \(x/L\) is at most
\[
 r_m(L)=(m+1)!\left[L e^{-L/2}/10^{m+2}
                 +\frac{1}{L^{m+1}(1-2(m+2)/L)}\right]
\]
on the log range in question. Split the integral at \(L/2\) in log coordinates; on \([L/2,L]\), use \(u^{-m-2}\le L^{-m-2}\exp(2(m+2)(L-u)/L)\), by integrating the derivative of \(-\log u\). If \(\epsilon_U,\epsilon_D\) are the indicated upper and lower \(\pi\)-error radii, let
\(e_U=\epsilon_U(L)+2500Le^{-L}+r_m(L)\), \(e_D=\epsilon_D(L-1)+2500(L-1)e^{-(L-1)}\).
The two uses of the exponential integral are at \(x\) and \(x/e\). Let \(d_k=[z^k](\sum_{j=0}^m j!z^j)^2\). Then for \(L\ge36.9\),
\[
 G(x) \ge \sum_{j=0}^{m-4}\frac{c_{j+4}}{L^j}
 -\sum_{k=m+1}^{2m}\frac{d_k}{L^{k-4}}
 -L^4\left[e_U(2A_m+e_U)+\frac{L}{L-1}e_D\right].
 \tag{R}
\]
Indeed \(G=L^4[(L/(L-1))(\pi(x/e)/(x/(e(L-1))))-(\pi(x)/(x/L))^2]\). Expand the smooth first term using \((1-1/L)^{-j-1}\) with nonnegative coefficients, retaining terms through degree \(m\) and subtract the full square. The degree \(k\le m\) of the difference is \(c_k\); \(c_0=\cdots=c_3=0\). The remaining coefficients in the square are deducted in full. Normalized \(\pi(x)\) is nonnegative, so squaring its positive upper bound is valid.

For the finite joins the verifier encloses (R) **minus the requested profile after cancelling its common coefficients** on closed rational log cells. Each accepted cell has strictly positive lower bound; subdivision terminates with the leaf counts and positive slack in `R-evidence.txt`. The branch changes are guarded by the entire-cell domain and the adjacent cells include their common endpoint. After the listed join, use the analytic tail. For \(P_n+d/L^{n+1}\), keep only the first unused positive term, multiply by \(L^{n+1}\), and bound all losses by their value at the join. For a constant below 1 just keep 1, and for the constant 1 keep \(14/L\) and multiply by \(L\). Positivity \(c_k>0\) for every \(k\ge4\) follows from \(c_k/k!=\sum_{i=0}^k1/i!-\sum_{i=0}^k1/\binom{k}{i}\): the second sum is at most \(2+2/k+2(k-3)/(k(k-1))\le 8/3\); the first is at least \(65/24\).

Here is the monotonicity argument for the losses. Each endpoint term after scaling is a positive sum of monomials times \(e^{-dL}\) (or (e^{-d(L-1)})), with exponent at least \(1/8\) and with non-exponential rational factors either decreasing, or bounded in the form \(L^j\) already accounted for. The endpoint/prefix terms have polynomial degree at most 3 in \(L\) before scaling; a term using \(v=L/2\) in the prefix is exactly such a monomial with negative powers allowed. At the joins \(L\ge240\), all resulting powers after multiplication by \(L^{4+n+1}\) have \(L-1>8(4+n+1+3)\) for \(n\le7\); thus these scaled terms decrease. For shifts, \(L^r(L-1)^s e^{-d(L-1)}\) decreases if \(L-1>(r+s)/d\) for \(r,s\ge0\); use negative powers as separate decreasing factors. For the smooth remainder's inverse-power part, after scaling the net power is nonpositive and \(1/[1-2(m+2)/(L-1)]\) decreases. \(A_m,L/(L-1),e_U\) are decreasing on this tail, so products in the squared error preserve the bound. The negative smooth coefficients are multiplied by at most \(L^8\), still negative net powers. These arguments justify the entire tail, not just the check at its left endpoint.

`higher.py` repeats the same tail proof for \(n\ge8\) with \(m=n+6, y=e^{2m+4}\), \(|K|<2y\) (both positive quantities in its definition are at most (2y), by (j!\le m^j) and (I_2\le y/\log 2)), and with \(10\) replaced by (2m+4) in \(r_m\). The code requires \(L-1\ge2\log y\) and a sufficient monotonicity threshold before testing. The argument provides an algorithm for arbitrary fixed finite order: the scaled loss tends to zero, while the first unused coefficient is positive. The binary search in that code proposes a sufficient onset; correctness uses only the final positive check and the analytic tail.

## 4. Exact last real sign failure, and old-result joins

Let \(n=38358837682\). Exact outputs from `endpoint.py`:
\[
 \pi(n)=\pi(n+1)=1644673232,\qquad
 \lfloor x/e\rfloor=14111427770,\quad \pi(x/e)=632207037
 \quad(n\le x\le n+1).
\]
The computation uses an ordinary Eratosthenes sieve up to \(\lfloor\sqrt n\rfloor+1\), inclusion–exclusion \(\varphi(x,a)=\varphi(x,a-1)-\varphi(\lfloor x/p_{a-1}\rfloor,a-1)\) for the integers surviving the first \(a\) primes (0-based indices), plus a wheel for the first six primes. For \(a=\pi(x^{1/4})\), survivors aside from 1 and primes are products of two or three primes with indices at least \(a\), sorted with repetition allowed. Counting quadruples is unnecessary because their least possible product exceeds \(x\). For pairs, fix \(i\) up to \(p_i^2\le x\), count \(\pi(x/p_i)-i\); for triples fix \(i\) up to \(p_i^3\le x\) and \(j\ge i\) up to \(p_j^2\le x/p_i\), count \(\pi(x/(p_ip_j))-j\). Subtract these from \(\varphi+a-1\). All recursive arguments are smaller, with exact integer roots/divisions. The short base case of \(\varphi\) counts only 1 and surviving primes when the next surviving prime squared exceeds \(x\).

Thus \(r\) is the unique solution in this unit interval of \(e r(632207037)/\log r=(1644673232)^2\); monotonicity of \(t/\log t\) for \(t>e\) and the two certified signs give the bracket. In fact \(R(n)\) is about (-14736927.9) with a strictly negative interval. Consequently the literal real reading of PT 2021 Theorem 2 starting at \(x>n\) cannot hold. We do not use that reading as a premise.

The Dudek–Platt §3.1 finite assertion of the largest **integer** failure up to \(10^{11}\), and its Lemma 3.4 restricted to integer inputs up to \(1.15\cdot10^{16}\), are inherited finite computations, not full-RH assertions. Their finite data and step conclusions are used at that trust tier. For a real \(x>e\) in \([k,k+1)\), \(\pi(x)=\pi(k)\) and both \(x/\log x\) and \(\pi(x/e)\) are nondecreasing, so \(R(x)\ge R(k)\). This joins the integer result to real \(x\), including the interval just below the large finite upper cutoff. Independently (R) verifies \(G>0\) on \([36.9,37]\) in log coordinates, overlapping the finite cutoff \((e^{36.9}<1.15\cdot10^{16}<e^{37})\). The 0.1 ray covers the rest. This proves the stated strict-sign result without treating the printed real endpoint as evidence.

The full quantitative lower envelope may additionally take any original valid direct \(\pi\) upper/lower box separately at \(x\) and \(x/e\) when forming the gap. In particular retain Dusart 5.1, 5.2 with their individual domains, FiniteRH p.4 Corollary 1, and PT 2021 Corollary 2 \(235x L^{.52}e^{-.8\sqrt L}\) for \(L\ge2000\), with each source's \(\operatorname{li}\). A comparison to \(I_2\) uses the corresponding constant, not an assumption that all li normalizations coincide. If the conventional principal-value li is used, \(\operatorname{li}(2)=\gamma+\log(\log 2)+\sum_{k\ge1}(\log 2)^k/(k\cdot k!)\) has absolute value \(<2\) by the convergent series and elementary bounds. These direct source boxes need not attain the quantitative profiles from (R). The strengthened \(B_1\) envelope is the maximum of all \(B_0\) profiles and its new profiles, so old bounded intervals are never lost.

## 5. Forward kernels, signed spectrum, and smaller product errors

Use \(u=\log t\) in log-coordinate integrals. Set \(F(u)=\psi(e^u)e^{-u}-1\),
\[
 F_0(L)=\sum_{n\le x}\frac{\Lambda(n)}{n\log n}-\log L-\gamma,\qquad
 F_1(L)=\sum_{n\le x}\frac{\Lambda(n)}n-L+\gamma,
\]
where the first sum starts at \(n=2\). To avoid index ambiguity, denote by \(W_j\) the centered weighted error with **weight \(t^{-1}(\log t)^{-j}\)**: \(W_0=F_1, W_1=F_0\). Partial summation with the boundary included yields
\[
 W_j(L)=L^{-j}F(L)-\int_L^\infty k_j(u)F(u)du,\quad
 k_j(u)=u^{-j}(1+j/u),\quad j=0,1. \tag{K}
\]
The centering constants follow from Dusart 5.6–5.7 and adding the absolutely convergent prime-power contributions. The limits and the integrals also follow from (B). Formula (K) holds for real \(x>1\); whether \(x\) is a prime power matters in the endpoint term, not a measure-zero change in the ordinary integral. Another exact identity is \(F_0(L)=F_1(L)/L-\int_L^\infty F_1(u)du/u^2\), by partial summation of the centered \(n^{-1}\Lambda(n)\) sum. The CH2 weighted bounds can therefore be used without the loss of integrating a constant relative error in \(\psi\) over the whole tail.

### Signed split

With the same \(T,T^\star\) as §2,
\[
 F(u)=-\sum_{\Re\rho\ge.745}\frac{e^{(\rho-1)u}}{\rho}+E(u),\qquad
 |E(u)|\le\sum_\nu b_\nu u^{n_\nu}e^{-d_\nu u}=:\mathcal R_a(u).
\]
Here the zero series includes both signs of the ordinate. Take the terms
\[
 (.04u^2+13u+2)e^{-u/2}+.02u^2e^{-.255u}
 +130(u/2)^4 e^{-(a+.16)u}+60((u/2)^2+u+2)e^{-(a+.5)u}.
\]
Indeed the low zeros and the Perron remainder are bounded by \(U+Je^{-.255u}\). For the high zeros omitted beyond \(T^\star\), integrate the density at \(s=.745\) from (T), using \(p=.68, d=.32, q=3.51, \log T=u/2-\log 6>28\). The log-power integral is at most \((\log T)^q T^{-d}/[d-q/\log T]\), since \((1+w/v)^q\le e^{qw/v}\). Here \(d-q/\log T>.19, 6^{.32}<2\) and \(c=6.1727\) (\(2\cdot6.1727\cdot2/.19<130\)); the second coefficient uses (2\cdot5\cdot6). The factor \(e^{-au}\) accounts for the real-part cap. With only Dusart's density replace 130, 60 by 220, 618; \(4.9\,3^{.68}<10.4\). The proof has no discontinuity issue because FKS 3.2 is for all real \(x\).

Termwise integration in (K) is justified by the convergent absolute reciprocal bound and the integrable majorant. For a high zero, integration by parts gives a bound \(2 k_j(L)e^{-(1-\Re\rho)L}/|\rho-1|\) on its integral before the \(1/\rho\) factor. Indeed \(k_j\) is positive nonincreasing, and \(\int_L^\infty|k_j'|\le k_j(L)\). As \(|\rho-1|\ge H\), the integrated error is tiny relative to the endpoint spectral term, rather than costing an extra factor of order \(1/a\). Consequently
\[
 L^j|W_j(L)|\le
 \left(1+\frac{2(1+j/L)}{H}\right)Z_\beta(L)
 +\sum_\nu b_\nu L^{n_\nu}e^{-d_\nu L}
     \left(1+\frac{1+j/L}{d_\nu-n_\nu/L}\right).
 \tag{M}
\]
This uses \(\int_L^\infty u^n e^{-du}dule L^n e^{-dL}/(d-n/L)\). The stronger signed treatment is important even when the unintegrated \(\psi\) bound has already been improved.

### Prime powers and conversion to products

Write \(D(t)=\psi(t)-\theta(t)\). The full omitted prime-power tail for weight \(t^{-1}(\log t)^{-j}\) is \(T_j(x)=\int_{(x,\infty)}t^{-1}(\log t)^{-j}dD(t)\). By positivity and parts,
\[
 0\le L^j T_j(x)\le 2.000000294e^{-L/2}+2.67e^{-2L/3}-D_-(L),
 \tag{T}
\]
where \(D_-=0\) is always allowed and for \(x\ge4\) we may use \(D_-=(1-\min(2.4646/L,15.86/L^2,166.64/L^3,2420.8/L^4))_+e^{-L/2}\). The lower bound on \(D(x)/x\) uses \(\theta\(\sqrt x\)\) and Dusart 4.2, with all four rows valid from \(\sqrt x=2\). For the integral upper, \(\int_L^\infty e^{-du}(u^{-j}+j u^{-j-1})dule e^{-dL}/(dL^j)\) for \(0<d<1\), by differentiating \(e^{-du}u^{-j}\); the endpoint term subtracts \(D(x)/(xL^j)\). This improves the crude integer prime-power estimates, including before spectral dominance.

Then \(E_w=W_0+T_0\), \(E_1=W_1+T_1\), and \(q=\log\mathcal Q=W_1+T_{1,\mathrm{tr}}\), the latter tail restricted to \(p\le x\) but \(p^k>x,k\ge2\). In particular \(0\le T_{1,\mathrm{tr}}\le T_1\). Equivalently \(q=E_1-A_{>x}\) with \(0\le A_{>x}=\sum_{p>x,k\ge2}1/(kp^k)\le1/(2\lfloor x\rfloor)\) by comparison to half the telescoping sum \(1/[n(n-1)]\). These are exact, with the claimed normalizers, not first-order approximations. A symmetric bound \(r\) for (|q|) yields \(\max(|\mathcal P-1|,|\mathcal Q-1|)\le e^r-1\le r e^r\). More finely if (q\in[l,v]), upper bound the two absolute errors by \(\max(e^v-1,1-e^l)\) and \(\max(e^{-l}-1,1-e^{-v})\), respectively in order \(\mathcal Q,\mathcal P\). All log boxes may be intersected first. The outputs are correlated.

### Whole rays and continuous asymptotic tradeoff

Add (T) to (M). For the power table multiply the scaled radius by \(e^{aL}\), use the harmless overestimate \(D_-=0\), and evaluate at \(L_0\). Every positive term in the resulting normalized error is nonincreasing: spectral exponents are nonnegative, \(d_\nu-a>0\) and \(n_\nu/(d_\nu-a)<L_0\), the denominators increase, (1+j/L) decreases, and the exponentiation multiplier for the products is decreasing too. This proves the whole ray. The runner `certify.py M` verifies the legacy conservative rows (see `M-ram-only.txt`); the exact constants in the table in §1 are all certified by the improved split in `repair.md` and `RAM_ONLY=1 /usr/bin/python3.10 refine.py`. The original under-transcribed spectral implementation is not part of the active proof.

For a second branch, define
\[
 C_R^*(s)=2\left[\frac{4.9\,3^p h^q e^{-dh}}{d-q/h}
      +51.5\frac{h^2+2h+2}{H}\right].
\]
It is an upper bound for the cumulative reciprocal count by the same log-power integral bound. Its logarithmic derivative is no more than 105 in absolute value on \([.745,7/8]\): for the nonconstant term bound it by \(2\log h+(8/3)(h+\log 3)+(8/3+2/h)/(.32-3.51/h)<105\), and the additive constant has derivative zero. Integrating the cumulative bound by parts in the *real part*, not the ordinate, thus gives for \(L>105\)
\[
 \sum_{\Re\rho\ge.745} |e^{(\rho-1)L}/\rho|
 \le C_R^*(\beta)e^{-aL}\frac{L}{L-105}.
 \tag{C}
\]
In detail the scaled bound is \(C_R^*(.745)e^{-(\beta-.745)L}+L\int_{.745}^\beta C_R^*(s)e^{-(\beta-s)L}ds\); bound \(C_R^*(s)\) by \(C_R^*(\beta)e^{105(\beta-s)}\), then add. Replace \(Z_\beta\) in (M) by the minimum of (Z) and (C). This gives the further rows with \(L_0\ge600\), again by monotonic normalized comparison (\(L/(L-105)\) decreases). It gives limiting upper coefficients \(C_R^*(7/8)<.006740\), \(C_R^*(27/32)<.118072\); the non-spectral terms vanish relative to the target. For the sharper signed-series limsup bound \(\limsup\le C(\beta)\), and its refinement at the full height, see the exact-kernel calculation in repair.md §2. In particular one cannot simply replace the finite multiplier in (M) by 1 at the limit. No boundary zero is asserted.

### Earlier polynomial joins

For the weighted error, CH2 bounds \(|F_1(L)|\le w(L)\) with \(.8e^{-L/2}\) on \(L\le27.6\) in the range used, and globally \(w_{\rm ch}=c+113.67e^{-L/2}\). The first is the scaled computation in CH2 Lemma 9.2 and proof (the proof explicitly discusses the error multiplied by \(\sqrt x\)); \(e^{27.6}<10^{12}+3\). For \(L\ge27.6\), CH2 Corollary 1.2 at \(T=10^7\) also gives \(w_{\rm fix}=3.142\cdot10^{-7}+33e^{-L/2}\). The two coefficients are outward bounds for \(\pi/(T-1)\) and the displayed log polynomial of Corollary 1.2, respectively. For \(F_0\) use \(w(L)/L+\int_L^\infty w(u)du/u^2\). Thus for \(L\le27.6\) an upper bound after multiplying by \(L\) is
\[
 .8e^{-L/2}(1+2/L)+L\min_{(\alpha,b)}\left(\frac{\alpha}{27.6}
                 +\frac{2b e^{-27.6/2}}{27.6^2}\right),
\]
where the two pairs \((\alpha,b)\) are the coefficients of \(w_{\rm ch}\) and \(w_{\rm fix}\). For \(L\ge27.6\) use the minimum of \(2\alpha+b e^{-L/2}(1+2/L)\) over those pairs. Use (T) and (M) too. The runner certify.py M bounds the polynomial radii on closed log cells up to 200 starting at \(L=16.05,16.25,16.45,16.7\) for the finite joins \(.19,.18,.16,.15\), and \(15.5,15.65,16,16.5\) for \(.27,.24,.21,.18\) (weighted), respectively. It also checks the four analytic-only polynomial rays listed in §1. On \(L\ge200\), \(L^2\) times the \(L^j\)-scaled radius in (M) plus the upper tail without subtraction decreases term by term; exponential conversion preserves the bound. This proves the entire analytic join.

The finite join to those log starts is independently checked to (20{,}000{,}000) by `finite.c`, which certifies boxes for the two constant sums and both products. The eight log starts used for the finite joins are below this finite upper bound. See `finite-proof.md` for the exact fixed-point argument and the meaning of the printed witnesses.

## 6. Pointwise envelopes and matched comparisons

For clarity, here is an entire-domain prescription, including ranges where a convenient power row is not smallest. In all branches only apply a source formula within its domain. The direct polynomial bounds of Dusart 5.6–5.9 and independently joined rows above are always retained. At very small \(x\) the prime sums or products themselves are finite and can alternatively be evaluated with the constant intervals in `finite-evidence.txt`; for \(1<x<2\) the prime sums are empty and the raw products are one.

* **Source Chebyshev minima.** For \(\psi\), take the applicable minima of FiniteRH Cor. 1, CH2 Cor. 1.2 for any admissible \(10^7\le T\le3000175332800\), Cor. 1.3, Lemma 9.2, \(10.3\), Dusart Thm. 3.3 and Table 1, FKS Cor. 1.4, Lemma 5.2 **restricted to \( .85\le L\le2100 \)** as proved in `repair.md`, and step values in its proof, Thms. 1.1–1.2 (in particular all applicable rows of Tables 5–6), and PT 2021 Thm. 1 (both radii from each row). Rows at a threshold inconsistent with the theorem's strict premise are not needed (\(L_0=1000\) in FKS 1.1–1.2); use its repaired Lemma 5.2 instead on that range. For \(1<x<2\), use the exact relative Chebyshev error \(-1\) when needed. `source-tables.json` records the tabulated arguments; a displayed rounded analytic value can safely be enlarged by \(1.001\) if needed for an outward table interpretation. For \(\theta\) include direct Dusart 4.2, FiniteRH Cor. 1, PT Cor. 1 and \(18\), and all transfers from \(\psi\) with the indicated prime-power correction. This is a portfolio minimum, not a claim of optimal tuning over all possible proofs.
* **Kernel minima.** In both treatments include (B) with the respective cap and all \(B_0\) branches. Include the signed boxes from (M) and (T), the continuous alternative (C), and the direct D02 \(\psi\) majorant only at its allowed threshold. If \(b(u)\) is a pointwise envelope for the absolute error in relative \(\psi\) or \(\theta\), the transformed weighted radius is \(b(L)L^{-j}+\int_L^\infty k_j(u)b(u)du\). For \(\psi\) this bounds \(W_j\), for \(\theta\) it directly bounds \(E_w\) \((j=0)\) or \(E_1\) \((j=1)\), by Dusart's identities (or partial summation). Intersect **before and after** integral transfer: take the minimum under the integral, as well as any independently smaller output bounds that are not unsigned transfers. For signed relative boxes \([l(u),v(u)]\), use endpoint lower minus integral of upper and endpoint upper minus integral of lower. The minimum functions are measurable (the tabulated branches are piecewise continuous; for a continuum of CH2 parameters it suffices to take a countable dense set and its one-sided endpoint limits). Integrate the cumulative envelopes which include an integrable branch from (B), or FKS 1.4 independently. For the unsigned reverse transfer from \(E_1\) to \(q\) use \([-r-A_{>x},r]\), and for a \(W_1\) radius use \([-r,r+T_1]\), then intersect and exponentiate as above. Similarly the signed \(W_0\) weighted tail box is \([-r,r+T_0]\). The separate direct CH2 bound on \(F_1\) and its transfer to \(F_0\) augment these, not substitute for them. The direct D02 unsigned kernel without the density argument, for example, gives
\[
 |W_0|\le e^{-aL}(L^2+L^2/a+2L/a^2+2/a^3)/64,\quad
 |W_1|\le e^{-aL}(L+(L+1)/a+1/a^2)/64,\quad a=5/32,\quad L\ge200 .
\]
The signed spectral table improves these by orders of magnitude (even the normalized endpoint cost of the direct input alone is \(L^2/64\ge625\) versus .226). The important advance is reducing the exponent by \(1/32\) **relative to the QRH-aware comparator**, not just beating the original inverse logarithms.

* **Whole-domain comparison.** The \(B_1\) envelope includes the \(B_0\) envelope identically, so no joins can make it worse, on their entire domains. Strict improvement for \(L\ge200\) can be proved against the enumerated finite original-output and transfer branches, not inferred from samples: every explicit original tabulated \(\psi\) radius in `source-tables.json` and the indicated original polynomial/exponential branches is at least \(.005e^{-L/8}\) on that matched domain. For constants check the onset (or 200), for \(A L^be^{-c\sqrt L}\) check the onset and use \(1/8-c/(2\sqrt L)>0\) in the logarithmic ratio; for inverse powers use \(1/8-k/L>0\). CH2's admissible finite-height branch has floor \(>1.047\cdot10^{-12}\). The terminal mesh coefficient in (Z) for \(B_0\) exceeds .005 (check in `comparison.py`), and \(C_R^*(7/8)>.005\). Thus each of the \(B_0\) transfers here has an endpoint radius at least the guard (divided by (L) for the normalized log quantities). One-sided prime-power boxes also contain both signs of this guard: for the \(\theta\)-sourced product box use \(q=E_1-A_{>x}\), for the \(\psi\)-sourced one \(q=W_1+T_{1,\rm tr}\); the endpoint \(\theta\) correction \(D_-,D_+\) is \(o(e^{-L/8})\) and is less than \(.001e^{-L/8}\) throughout this ray. Even allowing that subtraction, or applying \(1-e^{-r}\ge r-r^2/2\), a conservative surviving matched scaled guard is \(.002e^{-L/8}\). The direct \(B_0\) product bounds can be intersected in log coordinates using their logarithms; they also contain this smaller guard. The inequality \(.226e^{-200/32}<.002\) proves the claimed strict ordering against these branches; the original inverse-logarithm radii are also dominated simply by the decreasing ratio \(CL^2e^{-aL}\) after the listed onsets. This strict ordering is not a lower bound for actual prime errors, nor an extremal statement about unenumerated choices of analytic estimates, such as a new optimization of the parameters in FKS \(4.1\). The retained minima permit those legal original choices as additional boxes; the strict comparison here is to the enumerated explicit branches.
* **Where no gain is certified.** The low-input polynomial joins and real sign endpoint have no D02 dependence. A near-constant floor of the finite-height CH2 bound controls the intermediate ranges until (B)/(M) becomes smaller. The density and Perron estimates with a reduced cap remain too expensive around part of the intermediate log range to connect the entire early \(P_2,P_3,P_4\) components at those higher margins. For example the verified *lower-bound formula* (R) minus \(P_2\) is negative at \(L=150\) for both caps; that is a limitation of that formula, not a counterexample to the true \(P_2\) inequality. See diagnostics.py and NOTES.md for explicit failures of proposed lower-bound formulas and the scope of the remaining bottlenecks.

## 7. Reproduction and proof tiers

Run from the flat submission directory:
```
/usr/bin/python3.10 certify.py R
/usr/bin/python3.10 certify.py M
/usr/bin/python3.10 higher.py
/usr/bin/python3.10 endpoint.py
/usr/bin/python3.10 comparison.py
RAM_ONLY=1 /usr/bin/python3.10 comparison.py
RAM_ONLY=1 /usr/bin/python3.10 refine.py
RAM_ONLY=1 /usr/bin/python3.10 ramref.py
/usr/bin/gcc -O3 -std=c11 finite.c -o /work/finite
/work/finite
```
The decimal enclosure uses 40-digit directed rounding for arithmetic. Python Decimal exp/ln are correctly nearest-rounded; taking the neighboring contextual numbers outward encloses them. Closed-cell interval evaluation uses no assumptions about variation inside a cell beyond the proved enclosure and branch conditions. Machin's arctangent formula with alternating rational series bounds the \(\pi\) interval. These computations are independently reproducible ordinary numerical/integer certificates, not kernel-checked. Original QRH, the finite RH calculation and literature sign/weighted input have exactly their packet trust level. No quoted conditional full-RH Ramanujan conclusion is promoted to an unconditional premise. Neither a within-method \(B_0\) run nor any failure diagnostics constitute an independent blind baseline.
