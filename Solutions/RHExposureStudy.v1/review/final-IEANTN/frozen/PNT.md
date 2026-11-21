# PNT: admissible variable height, center correction, and signed transfers

Write \(L=\log x>0\), \(a=1/(8\pi)\);
\(\operatorname{li}(x)=\mathrm{Li}_2(x)+c_2\), where \(c_2=\operatorname{li}(2)\).
All new ray statements assume the pinned Mathlib RH. Prime functions have
inclusive upper endpoints. Use the following published inputs only on their domains.

| Quantity | Envelope and input | Domain |
|---|---|---|
| \(\lvert\psi-x\rvert\) | \(.94\sqrt x\), Büthe 1511.02032v2 Thm 2 (1.5) | \(11<x\le10^{19}\) |
| \(\lvert\psi-x\rvert\) | \(a\sqrt x L^2\), Büthe 1410.7015v4 Thm 2 + RH | \(x>59\) |
| \(\lvert\psi-x\rvert\) | \(\sqrt x(aL^2-L/(2\pi)+1.465\log L+1.2325)\), Lee–Nosal Thm 1.1 | \(x\ge11\) |
| \(\lvert\psi-x\rvert\) | \(a\sqrt x L(L-\log L)\), Lee–Nosal Thm 1.2 | \(x\ge101\) |
| \(x-\theta(x)\) | between \(.05\sqrt x\) and \(1.95\sqrt x\), Büthe (1.6),(1.7) | \(1423\le x\le10^{19}\) |
| \(\lvert\theta-x\rvert\) | \(a\sqrt x L^2\), Büthe 2016 Thm 2 + RH | \(x>599\) |
| \(\lvert\theta-x\rvert\) | \(a\sqrt x L(L-\log L)\), Lee–Nosal Thm 1.2 | \(x\ge2657\) |
| \(\pi-\operatorname{li}\) | \(-q(L)\sqrt x/L\le \pi-\operatorname{li}<0\), \(q(L)=1.95+3.9/L+19.5/L^2\), Büthe (1.9),(1.10) | \(2\le x\le10^{19}\) |
| \(\lvert\pi-\operatorname{li}\rvert\) | \(a\sqrt x L\), Schoenfeld / Büthe Eq. (7.2) + RH | \(x>2657\) (Schoenfeld \(x\ge2657\)) |
| \(\lvert\pi-\operatorname{li}\rvert\) | \(a\sqrt x L\), Johnston Thm 3.2 & Cor. 3.3 (published finite verification) | \(2657\le x\le1.101\cdot10^{26}\) |

For bands converted to \(\pi-\mathrm{Li}_2\), add \(c_2\) to both
ends, or \(\lvert c_2\rvert\) to an absolute bound.
Rosser–Schoenfeld 1962 Thm 12 (3.35) gives \(0\le\theta\le\psi\le1.03883x\)
for \(x>0\).

## The new ray \(x\ge e^{34}\)
Let \(u=L/2-\log L+\log(10/\pi)\), \(A(L)=.158L+(u^2-u/3)/(2\pi)\)
and \(r=\psi(x)-x\). The resulting bands are
\[
\begin{aligned}
 |r|&\le A(L)\sqrt x,\\
 r-1.01\sqrt x&\le\theta(x)-x\le r-.99\sqrt x,\\
 r/L-1.10\sqrt x/L-C(x)&\le\pi(x)-\operatorname{li}(x)
 \le r/L-.99\sqrt x/L+C(x),\\
 C(x)&=14+.278\sqrt x/L^2.
\end{aligned}
\]
In the conventions \(E_\psi=|\psi-x|/x\) and
\(E_\pi=L|\pi-\mathrm{Li}_2|/x\), these give \(E_\psi\le A(L)/\sqrt x\)
and \(E_\pi\le(A(L)+1.10+.278/L)/\sqrt x+(14+|c_2|)L/x\).
The actual \(r\) matters when its sign is known.

### Variable height and pointwise comparison

Chirre–Helfgott arXiv:2512.15709v1 Cor. 1.2 requires \(T\ge10^7\),
\(x>\max(T,10^9)\), and RH to height \(T\).
Set \(T=20\sqrt x/L\), increasing for \(L\ge34\); already \(T>10^7\)
at 34 and \(T<x\), \(x>10^9\). PNTStudy.height_conditions is a
non-grid proof, and PNTStudy.actual_psi consumes the actual CH2
Cor. 1.2 and mainFactor_bounds proofs. That route retains 13 named
inputs, including Platt's inverse-ordinate sum; RH does not supply them here.

The center factor obeys \(1\le(\pi/T)\coth(\pi/T)\le1+(\pi/T)^2\)
for \(T\ge\pi\). The resulting bound in units of \(\sqrt x\) is
\(\sqrt x[\pi/(T-1)+(\pi/T)^2]+(u^2-u/3)/(2\pi)\).
Since \(\sqrt x=TL/20\), the first term is at most
\((\pi(1+1/(10^7-1))+\pi^2/10^7)L/20<.158L\).

For comparison with Lee–Nosal 1.2, set \(k=\log(10/\pi)\),
\(v=\log L-k\). The difference \(a L(L-\log L)-A(L)\),
times \(8\pi\), equals
\[
 L(3\log L-4k+2/3-8\pi\cdot.158)-4v^2-(4/3)v.
\]
Use \(1.15<k<1.16,\ 3.52<\log34<3.53,\ 3.14<\pi<22/7\).
The bracket exceeds 2.61, while \(v>2\) and both \(v/L,v^2/L\)
decrease, giving remaining cost \(<.77L\). The gain \(>1.8L/(8\pi)>2.4\)
survives the theta/π allowances. LN 1.2 is smaller than 1.1 for
\(L\ge e^4\); on \([34,e^4]\) the difference (1.1 minus 1.2) is
at least \(-ae^4(.48)+1.465(3.52)+1.2325>0\).
Büthe's finite bounds often give a better minimum, and variable
height does not enlarge an unconditional published Johnston domain.

### Prime powers and integral transfer

For theta, \(\psi-\theta\ge\theta(\sqrt x)\) by squares.
The Mathlib Costa Pereira upper bound is
\(\psi-\theta\le\psi(\sqrt x)+\psi(x^{1/3})+\psi(x^{1/5})\).
Use Schoenfeld at the square root for both functions and
Rosser–Schoenfeld (3.35) at the other two. In units of \(\sqrt x\)
the square-root relative error is \(<.003\) and the two smaller-root
costs total \(1.03883(e^{-L/6}+e^{-3L/10})<.004\).
This retains the square main term, rather than paying \(2\sqrt x\log x\).

For \(J(t)=\sum_{k\ge1}\pi(t^{1/k})/k\), Stieltjes partial summation
from \(a_0=e^8\) gives
\[
 J(x)-\operatorname{li}(x)-r/L
 = J(a_0)-\operatorname{li}(a_0)-(\psi(a_0)-a_0)/8
   +\int_{a_0}^x \frac{\psi(t)-t}{t(\log t)^2}\,dt.
\]
Büthe 2018 Thm 2 (1.8),(1.5) gives absolute anchor \(\le1.94e^4/8\).
Integrate by parts using the primitive from Grenié–Molteni Thm 1.1
(Weighted.md): for its \(c=.0462\) term use
\((\sqrt t/(\log t)^2)'\ge1/(4\sqrt t(\log t)^2)\) for \(t\ge a_0\).
Differentiating the original weight costs \(1+2/\log t\le5/4\).
For its \(b=1.838\) term use \(\int_{a_0}^\infty dt/(t\log^2t)=1/8\).
The coefficient on \(\sqrt x/L^2\) is \(6c=.2772<.278\), and the
constant is at most \(1.94e^4/8+c e^4/64+2b/64+5b/32<14\).
Direct integration of the pointwise PNT error loses this gain.

For \(J-\pi\) keep \(\pi(\sqrt x)/2\). Using the normalized li
barriers \(1\le w(s)\le p_3(s)+72/s^4\) for \(s\ge17\)
(Ramanujan.md) and Schoenfeld, the square contribution in units
of \(\sqrt x/L\) is between \(1-.003\) and
\(p_3(17)+72/17^4+a\cdot17^2e^{-17/2}<1.071\).
For \(t\ge2\), \(\pi(t)\le2t/\log t\):
combine \(w(\log t)<3/2\) with Büthe (1.10) up to \(10^{19}\),
and with Schoenfeld above it (relative correction \(<.5\), decreasing
above \(\log t=43\)). Thus the \(k\ge3\) contribution in the same units
is at most \(2(e^{-L/6}+(L/\log 2)e^{-L/4})<.028\).
Subtracting the resulting positive band yields the stated π band.

## Boundary and rejected shortcuts

* FullRH.sqrt_log_fallback legitimately chooses \(\beta=1/2\) in
  CH2.v5 fixed-strip, onset \(e^{32}\); this is weaker by \(4\pi\)
  than Schoenfeld.
* FullRH.classical_076 uses RH and the separate LowZeroes first-ordinate
  exclusion to get the closed region with \(R=.76,t_0=2\).
  Below 14.134725 no zero exists by that contract; above it
  \(.76\log t>2\). In the closed convention \(R=2/\log\gamma_1\)
  would fail at a zero of ordinate \(\gamma_1\) in the domain.
  Positive ordinate excludes the pole and the negative even zeros.
  No FKS Table 8 reevaluation follows.
* NetworkReuse.fks_density_from_rh uses an empty index set, not a bare
  tsum equality or substitution \(\beta=1/2\) into a \(7/8\)-only theorem.
* CH2 §10.3 suggests retaining the signed spectral polynomial instead
  of \(C_T\). We did not evaluate it: RH supplies placement, not a
  certified list of ordinates and a finite interpolation certificate.

### Reduced independent premises, with a bounded price in the coefficient

There is a second actual Lean route with \(\psi\) coefficient \(A(L)+.821\)
instead of \(A(L)\). PNTClosed.sharpened consumes the actual existing
CH2 Proposition 2.4 upper and lower, Gamma strip, and zeta
log-derivative functional equation proofs. It leaves RH and eight
explicit analytic predicates, not a separate inverse-ordinate-sum
premise. At the level of published inputs the +.821 variant still beats
the same Lee–Nosal envelope after transferring to theta and pi on
\(x\ge e^{34}\): the gain was \(>2.4\), and \(.821+1.10+.278/L+
14L/\sqrt x<2.4\) by monotonicity. See Ramanujan.md for the stronger
.076 replacing .278 in the pi transfer.

The arithmetic goes through the *actual* normalized contribution of
the low zero block. Apply the existing CH2Section7Z.lehman_antitone
with \(\phi(t)=1/t,\ t_0=2\pi,\ t_1=20000\). At \(2\pi\) the small
RvM inequality gives \(N(2\pi)=0\) by integrality since the main term is
\(-1/8\). The existing proof of finiteness is used explicitly;
every weight on the low set then has sum zero (nonnegative integer
multiplicities). For the remaining sum Lehman gives, after multiplying
by two,
\[
2\sum_{0<\gamma\le20000}\gamma^{-1}\le
\frac{\log^2(20000/(2\pi))}{2\pi}+
\frac25\left(\frac{1}{2\pi}-\frac1{20000}\right)+
\frac{\log(2\pi)/5+2-1/8}{\pi}\le11.1404 .
\]
All these steps are checked in LooseLowSum.lean. The previous 10.3194
bound cannot be used from the coarse count alone. The price of a
weaker upper bound is exactly .821 in CH2's coefficient of \(\sqrt x\).
In the adapted sections the inverse-ordinate term enters the scaled
zero bound additively, while the \(1/\sqrt x\) factor is maintained
through the contour finite-height shift and the \(\sigma=0\) limit.
The proof generator reconstructs three verified adapted theorem slices
from the actual pinned source, preserving all existing untouched
proofs and exact statement definitions. The intermediate delta is
transported explicitly, not justified by lowering an inapplicable
regime threshold. This removes a numerical input rather than
recomputing it. Laurent.md gives a further mathematical recovery of
the coefficient-sign premise; that extra removal is not in the
closed Lean chain.


The verified ThetaSigned path proves the same signed prime-power band
without the supplemental Rosser–Schoenfeld (3.35) input: apply the actual
Büthe finite-height psi adapter under RH at the three roots (all exceed
59). The two smaller roots get a uniform .08 relative allowance
and the square root .004, from monotonicity of \(u^2e^{-u/2}\).
The upper Costa Pereira form has powers 2, 3, 5, and the lower form
powers 2, 3, 7, all nonnegative. Thus the signed .99 and 1.01 bands
and theta_relay hold in Lean on the same ray. Its input coefficient
can be the output of PNTClosed.sharpened, not a fresh theta assumption.

### Two-range RvM variant: an analytic improvement to \(A+.332\)

The verified \(A+.821\) used the same coarse RvM information across
the full range. A written variant uses the small error bound through
280, not just to show \(N(2\pi)=0\). Put \(a=2\pi,\ b=280,\ H=20000\)
and \(M(t)=(t/a)(\log(t/a)-1)+7/8\).
Closed-count Stieltjes summation, including a possible zero at \(H\),
gives
\[
 2\sum_{0<\gamma\le H}\frac1\gamma
 = \frac{2N(H)}{H}+2\int_a^H \frac{N(t)}{t^2}\,dt .
\]
The main term's contribution is \(\log^2(H/a)/a+2M(a)/a\),
since \(M'(t)=\log(t/a)/a\). For the remaining part, use
\(N(t)-M(t)\le1\) on \([a,b]\), and
\(N(t)-M(t)\le(\log t)/5+2\) on \([b,H]\) and at \(H\).
The antiderivative of \((\log t/5+2)t^{-2}\) is
\(-(\log t/5+11/5)/t\). Hence the entire right side is at most
\[
 \frac{\log^2(H/a)}a+\frac{7}{4a}
   +\frac{2}{b}\left(\frac{\log b}{5}+\frac65\right)
   -\frac{2}{5H} < 10.651 .
\]
The last check uses the already verified \(\log(H/a)<8.066\),
\(\pi>3.141592\), and \(\log b<6\). Substituting 10.651 in the
same additive spectral step in CH2 costs at most .332 compared
with 10.3194, so gives \(A(L)+.332\) under RH and the same analytic
inputs as the looser route. This last propagation is a written
derivation, not a new compiled replacement for PNTClosed.sharpened.
