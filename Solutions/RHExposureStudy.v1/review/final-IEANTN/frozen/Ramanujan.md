# Ramanujan: quantitative real rays and an exact local crossing

Let \(G(x)=ex\,\pi(x/e)/\log x-\pi(x)^2\) and
\(R_G(x)=(\log x)^6G(x)/x^2\). Under the specified RH, a first route
proves \(R_G(x)\ge1/25\) for every real \(x\ge640000000000\).
For \(L=\log x\ge42\) the stronger bound is \(R_G\ge B(L)-D(L)\), where
\[
\begin{aligned}
 B(L)&=1+14/L+145/L^2+1412/L^3-1/1000,\\
 D(L)&=aL^5(L-1)e^{(1-L)/2}+(21/10)aL^6e^{-L/2}+a^2L^8e^{-L},
 \qquad a=1/(8\pi).
\end{aligned}
\]
In particular \(R_G>.379\) there. The real-ray proof consists of
a written analytic derivation and exact rational scalar execution
(ram_cert.py, RamanujanRun.txt), not a whole-theorem Lean replay.
Use Büthe 1511.02032v2 Thm 2 (1.8)–(1.10) and Table 2 (PDF p. 16,
§6.1) on their published finite domain, and Schoenfeld's conditional
\(\pi\) bound on the tail (also Dudek–Platt Thm 3.1; Büthe
1410.7015v4 Thm 2 Eq. (7.2) with the exact RH adapter).
The analytic comparison uses \(\operatorname{li}(e^L)=\operatorname{Ei}(L)\),
not \(\mathrm{Li}_2(e^L)\).

## Couple the Li terms before bounding

Write \(w(L)=Le^{-L}\operatorname{li}(e^L)\), \(p_N(L)=\sum_{k=0}^N k!/L^k\).
For \(A=w/L\), \(r=A-p_N/L\), we have \(A'+A=1/L\) and
\(r'+r=(N+1)!/L^{N+2}\). Given \(a_0>N+2\),
\(0\le r(a_0)\le C(N+1)!/a_0^{N+2}\), and
\(C(1-(N+2)/a_0)\ge1\), integrating-factor comparison yields
\(p_N\le w\le p_N+C(N+1)!/L^{N+1}\) for \(L\ge a_0\).
Use \((N,a_0,C)=(3,13,3),(20,26,7)\); setup() certifies the anchors.
For the auxiliary \(w(s)<3/2\) on \(s>0\), the derivative of
\(3e^s/(2s)-\operatorname{Ei}(s)\) has the sign of \(s-3\);
its certified minimum at 3 is positive.

The li-only normalized gap is \(L^4[(L/(L-1))w(L-1)-w(L)^2]\).
With \(u=1/L\), the lower-bound expansion of the first term in brackets
is \(\sum_{k=0}^{20}k!u^k/(1-u)^{k+1}\), all positive coefficients.
Subtract the square \(p_{20}^2\) coefficientwise: degrees 0–3 cancel,
degrees 4–7 have \(1,14,145,1412\), degrees 8–20 are positive.
Discard those last positive terms and bound the square terms past
20 after scaling by \(L^4\) at \(L=26\). The increase from the
upper remainder for \(w\), also in scaled units, is at most
\((11/5)\delta+\delta^2\), \(\delta=7\cdot21!/26^{17}\),
since \(p_{20}<11/10\). Total discarded error is below \(1/1000\).
This proves \(B(L)\) for \(L\ge27\), including the shifted argument.

## Recover signed deficits for each slab

Let \(z=\log t\), \(q(z)=1.95+3.9/z+19.5/z^2\), and
\(d(t)=(\operatorname{li}(t)-\pi(t))z/\sqrt t\).
For \(26\le z\le42\), decompose \(d=d_J+P\), with \(d_J\)
using \(J(t)=\sum_{k\ge1}\pi(t^{1/k})/k\) in place of \(\pi\) and
\(P=z e^{-z/2}\sum_{k\ge2}\pi(e^{z/k})/k\).
Büthe (1.9) gives the lower bound \(p_3(z/2)-q(z/2)e^{-z/4}\)
from the square term alone, and (1.10) its upper bound
\(p_3(z/2)+72/(z/2)^4\). For \(k>2\), (1.10) and \(w<3/2\)
bound each term by \((3/2)e^{-z(1/2-1/k)}\) (zero for a root below 2).
Sum \(k=3,\dots,10\) and bound the rest by
\(96e^{-z(1/2-1/11)}\), since \(42<64\log2\).
Intersect the resulting interval for \(d\) with \(0\le d\le q\).

For a slab \(L\in[l,u]\), enclose \(x\) in \([a_-,a_+]\) and \(x/e\)
in \([a_-/e_{\rm hi},a_+/e_{\rm lo}]\). For the Table 2 lower bound
on the first enclosure choose the largest level whose qualifying
closed rows cover it; for the upper bound on the second choose the
smallest level with a cover. Include the global (1.8) row
\([2,10^{19}]\) with levels \([-1,1]\). The local table matches
Buthe.v1.table_2_interval_bounds, not its globalized output.
Use the endpoints of each decreasing term separately; their
difference need not be monotone. With \(c\ge0\) the lower bound for
\(d(x)\), \(d\ge0\) the upper bound for \(d(x/e)\), set
\(F=cL^4 e^{-L/2}\), \(H=dL^5e^{(1-L)/2}/(L-1)\). Then
\[
 R_G(x)\ge B(L)-H+2w(L)F-F^2/L^4 .
\]
The upper bound for \(\pi(x)\) being squared is nonnegative
because it bounds the nonnegative actual count. Both \(F,H\)
decrease for fixed \(c,d\) on a slab, and \(w(L)\ge1+1/u\).
This proves the continuous enclosure evaluated by cell().
The endpoint \(L=42\) is below \(10^{19}\) in \(x\) coordinates.

## Rational certificates and tail

The exponential enclosure uses degree 155 Taylor for \(0\le x\le44\),
with tail at most \(t_{155}x/(156-x)\) by a geometric majorant.
Negative values use positive reciprocal enclosures. Rounding outward
at \(10^{-44}\) is exact rational. The Ei anchor uses
\(\gamma+\log s+\sum_{k\ge1}s^k/(k\,k!)\), geometric tail control,
a 35-term atanh log enclosure after reduction by powers of two,
and a harmonic bracket for \(\gamma\). The adaptive checker accepts
only with a scalar lower bound \(\ge1/25\), discards only if the
enlarged \(x\)-box is entirely below the onset, otherwise bisects.
The uniform comparison tiles \([27,42]\) at step .01 using the
same slab evaluator. Neither tests only sampled prime-count points.

On the tail Schoenfeld bounds the absolute error in \(Le^{-L}\pi(e^L)\)
around \(w(L)\) by \(aL^2e^{-L/2}\) (also at \(L-1\)).
Since \(w(L)\le21/20\), subtracting the losses yields \(D\).
Every term of \(D\) decreases for \(L\ge42\); for the first
use \(5/L+1/(L-1)<1/2\). The rational code checks \(D(42)<.62\)
using \(\pi>3.14\), so \(B(L)-D(L)>.379\).

Dudek–Platt v1 Lemma 3.2 advertises the analytic cut \(1.15\cdot10^{16}\);
their Theorem 1.3 concerns the largest integer failure. A finite
\(\pi<\operatorname{li}\) sign cannot be extrapolated to the RH tail.
Compared with the old IEANTN CoupledLargeMargin cut \(1.25\cdot10^{12}\),
this route exploits local Table 2 signs and prime powers instead of
a generic pointwise theta deficit. Johnston §5 uses many fine steps
of the unscaled gap, whereas coupling li first allows large slab widths.
This is not a claim of measured whole-proof speedup or a replacement
of the older early finite computations.

## Exact real crossing (not a jump of either count)

Let \(A=38358837682\). CriticalSourceClosed.p_source and q_source
are actual inherited source executions. On the entire closed unit
\([A,A+1]\) we have \(\pi(x)=1644673232,\ \pi(x/e)=632207037\).
The first floor is either \(A\) or \(A+1\), and \(A+1\) is composite
(factor 2521). The shifted floor is \(14111427770\) throughout,
using FiniteExpLinked.source_outputs_enclose_e and the old actual C
exponential executions. Hence
\[
 G(x)=e(632207037)x/\log x-(1644673232)^2
\]
is continuous and strictly increasing on the unit. The inherited
source-linked endpoint signs give a unique zero \(z\) and \(G>0\)
on the unit exactly above \(z\). RealCrossing.lean checks the local
claim without RH. A separate exact-rational run (crossing_cert.py)
gives \(38358837682.21792636514465772878< z <
38358837682.21792636514465772879\); this finer bracket is not a
source-first proof of all crossing arithmetic.

With Johnston Thm 5.1 on its published all-real interval
\([38358837683,e^{103}]\), the RH ray overlaps and gives \(G>0\)
for every \(x>z\). Thus \(z\) is the largest real failure of the
strict inequality and \(A\) is the largest integer failure.
RealCrossing.last_real checks the assembly with finite and analytic
providers explicit. This does not independently verify the whole
Johnston prefix. The old local-million verification has a disjoint
domain from the remaining prefix obligations.

CoefficientPV.lean binds actual rh_coeff.c to a typed restricted
C AST and consumes checked scalar executions in the degree-20
coefficient polynomial. This is function-level source-first PV,
not verification of the Python slab program or the C compiler.

## Second, earlier ray: Table 1 plus the signed integrated spectrum

With the same RH and right-continuous functions, a second computation
and derivation prove
\[
 R_G(x)\ge 1/1000\quad (x\ge610000000000).
\]
It does **not rely on Büthe's Table 2**: it uses the \(\psi\) Table 1,
Theorem 2 (1.5), (1.8) for one anchor, (1.9) and (1.10), the integrated
explicit formula of Grenié–Molteni Eq. (1.3a) for \(\mathbf Q\), and the
analytic zeta inverse-square identity from Weighted.md, not a numerical
zero sum. It still uses the Schoenfeld RH tail for \(\log x\ge42\).
The earlier ray and the larger-margin Table 2 ray are distinct results.
The rational run accepts 11 nonempty slabs at \(6.1\cdot10^{11}\);
it fails the depth-30 control at \(6.0\cdot10^{11}\). The failed control
is not a counterexample to the prime inequality.

Here is the strengthened J transfer replacing the .278 coefficient
of PNT.md. For \(L=\log x\ge26\) and \(a_0=e^8\), integrate
\((\psi(t)-t)/(t\log^2t)\) from \(a_0\) to \(x\), using the exact
primitive before taking absolute values. An individual zero contributes
the negative of
\[
 \frac{x^\rho}{\rho^2L^2}-\frac{a_0^\rho}{\rho^2\,8^2}
       +\frac{2}{\rho^2}\int_{a_0}^x\frac{t^{\rho-1}}{\log^3t}\,dt .
\]
To justify this formula do integration by parts first with the
absolutely summable primitive, then integrate the term
\(t^{\rho-1}/\log^2t\) for each zero by parts once more. The bound
\(\sum_\rho|\rho|^{-2}<.047\) and uniform integrability on this finite
positive interval justify the resulting sum. On \(t\ge a_0\),
\((\sqrt t/\log^3t)'\ge1/(8\sqrt t\log^3t)\).
The real \(-\log(2\pi)\) and trivial-zero terms together contribute
at most \(1.838/8\) in modulus. Indeed their integrand has sign
negative there since \(-\tfrac12\log(1-t^{-2})\) is positive and smaller
than \(\log(2\pi)\). The absolute anchor is \(\le1.94 e^4/8\).
Therefore
\[
 |J(x)-\operatorname{li}(x)-(\psi(x)-x)/L|
 \le 14+.076\sqrt x/L^2 ,
\]
using \(.047(1+16/L)\le.076\) and
\(1.94e^4/8+.047 e^4/64+1.838/8<14\).
This is also a replacement for \(C(x)\) in the PNT signed count band,
even when the Table 1 range is not applicable, since the anchor
alone is within Büthe's finite range.

For \(26\le L\le42\), the Table 1 level of \((x-\psi(x))/\sqrt x\)
now controls \(d_J(x)\) to accuracy \(.076/L+14Le^{-L/2}\).
Re-use the same enclosing slab and covering algorithm. The square
prime-power term uses the sharper barriers \(p_8\le w\le
p_8+5\cdot9!/s^9\) for \(s\ge13\). Add k=3,4,5 to the *lower* power bound,
using \(w(s)\ge p_3(s)\) for \(s\ge5\), obtained by the same lower
integrating-factor comparison, with the certified anchor at 5.
For the upper bound at those k use \(w(s)\le p_1(s)+6/s^2\) from its
barrier at 5. The other powers are handled as before. The degree-20
positive coefficients from the same polynomial proof are now all
retained, not discarded from degree 8 onwards. In the \(2wF\) term
use \(w(\ell)\ge p_{20}(u)\) on \([l,u]\). The rest of the scalar
proof and the \(\ell\ge42\) tail are unchanged.
RefinedRamRun.txt records exact adaptive evidence with this tighter
input shape. No additional prime-count data was supplied.

## Reduced finite directed-count obligation

FiniteClip.lean reuses the actual strict-cell theorem by replacing the
stored \(P,Q\) by the unknown mathematical counts *in the proof*, not in
the executable data. The stored strict inequality transfers whenever
\(\pi(\mathrm{next}-1)\le P\) and \(Q\le\pi(j)\), in these directions
only. It consumes the old exact scalar/chain contract without requiring
count equality, and asks for those directed facts only on cells whose
left endpoint precedes the analytic cut. Thus no full-row resieving
is mathematically required above the cut, and no row scalar values or
source-files are modified.

PrefixReduction.txt is a manifest-only census (not mathematical truth
for prime counts): the older 1.25e12 transition demands up to 1,642,496
rows of the pinned 1,755,663-cell scalar certificate; the 6.4e11
transition uses at most 1,241,088. The second earlier cut reduces that
further. This is a reduction in the requested finite workload, not
a proved reduction in actual runtime or a completion of the remaining
directed count obligations. The published all-real result assembled
using Johnston remains separate from a possible full source-first replay.


## Non-grid quantitative recovery over Johnston's whole analytic range

Unconditionally using the published Platt–Trudgian height verification
\(T=3\cdot10^{12}\) as in Johnston, the tail proof does not require
RH itself for \(e^{42}\le x\le e^{103}\). The exact same formula
\(R_G(x)\ge B(L)-D_a(L)\) applies whenever both \(x\) and \(x/e\) are in
a permitted Johnston range with \(|\pi-\operatorname{li}|\le a\sqrt x L\).
Here \(D_a\) denotes the earlier \(D\) with that \(a\) substituted.
For \(L\in[42,59]\), use Johnston Theorem 3.2 at \(a=1/(8\pi)\).
The height requirement \(9.06^2e^L/(L(\log L)^2)\le T^2\) increases
from \(L=41\), and holds at 59. Both endpoints exceed 2657.
The normalized margin exceeds .379 throughout this slab.

For the eight consecutive closed slabs with endpoints
\(59,69,74,79,84,89,93,98,103\), use successively
\(a=1,10,100,10^3,10^4,10^5,10^6,10^7\) and the corresponding
\(K\) from Johnston Thm 4.1 Table 2. His requirement after squaring is
\(K^2 e^L/L^3\le T^2\), increasing for \(L\ge3\).
The lower endpoint \(L-1\) at \(x/e\) also satisfies it even across a
slab boundary, since the same theorem is valid for every smaller
admissible height down to the stated \(x\ge2\) here (we only use
heights \(\ge58\)). The eight right endpoints pass the required test.
Check \(D_a\) at each left endpoint: all are \(<.025\),
so \(R_G>.974\) on these slabs. The tail losses are decreasing for
each fixed \(a\), not across the row jumps.

This is a quantitative and verification improvement over using
Johnston's many fine steps of the unscaled gap in this range. It uses
his published analytic/count prerequisites, not a reproduction of
all his sources' numerical verifications. All nine scalar range
checks and losses are recorded in JohnstonTailRun.txt; no prime
counts at the slab boundaries are computed here. In the early
Table 2 route, the part with \(L\le42\) is already unconditional with
Büthe's computed inputs, so it joins this non-grid unconditional tail
from \(x=6.4\cdot10^{11}\) through \(e^{103}\). We do not independently
verify the earlier prefix of Johnston Theorem 5.1.

CrossingBracket.lean checks a narrower *formal* result than the Python
decimal calculation in one respect and a stronger one in trust:
the larger bracket \((38358837682.217926,38358837682.217927)\) is
proved in Lean with the already verified actual count/exponential
executions, and kernel-checked analytic atanh logarithm sums. No
arbitrary-precision native evaluation axiom is used here; the
20-place bracket remains separate exact rational evidence.
