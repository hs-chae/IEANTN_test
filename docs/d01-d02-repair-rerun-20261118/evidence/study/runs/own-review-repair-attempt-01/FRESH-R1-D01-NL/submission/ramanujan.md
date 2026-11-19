# Ramanujan gap

All results below use B0; see psi.md for why the new assumption changes none of them. Write \(L=\log x\) and \(G(L)=L^6 R(x)/x^2\).

## Results and comparisons

1. **Real positivity.** Let \(A=38358837682\). Define \(x_*\) as the unique solution in \((A,A+1)\) of
   \[
   e\,632207037\,x_*/\log x_*=(1644673232)^2 .
   \]
   Then \(A+.21792<x_*<A+.21794\), \(R(x_*)=0\), and \(R(x)>0\) for all real \(x>x_*\). The largest failing integer is \(A\); the largest failing real is \(x_*\). The finite integer coverage below the analytic range is at inherited literature trust, as detailed below. The real endpoint computation itself is separate.
2. **Bounded intervals and whole rays.** The following are strict bounds \(G(L)>c\); both displayed log endpoints are included. The one-sided rows have upper endpoint \(39.32\).

   | Start \(L\) | End \(L\) | \(c\) |
   |---:|---:|---:|
   |36.72|39.32|.003|
   |36.74|39.32|.013|
   |36.80|39.32|.040|
   |37|39.32|.130|
   |37.5|39.32|.340|
   |38|39.32|.510|
   |39|39.32|.788|
   |39.31|\(\infty\)|.080|
   |40|\(\infty\)|.370|
   |41|\(\infty\)|.680|
   |42|\(\infty\)|.898|
   |42.65|\(\infty\)|1|
   |43|59|1.04|
   |44|59|1.14|
   |46|59|1.25|
   |47.5|56.5|1.30|

   The overlapping first and second groups give whole rays at margins .003, .013, .04 from the same listed early onsets, and guarantee .08 from \(L=37\) onward. The higher early margins in the first group are bounded-interval tradeoffs, not whole-ray assertions. The pointwise profile below often improves the rounded entries.
3. **Higher-order profiles on rays.** For \(L\ge47.25\), \(G(L)>1+14/L\). For each row \((a,k,c)\) below,
   \[
   G(L)>\sum_{j=4}^{k-1}C_j L^{4-j}+c L^{4-k}\qquad(L\ge a),
   \quad C_j=\sum_{i=0}^{j}i!\binom ji-\sum_{i=0}^{j}i!(j-i)! .
   \]
   In particular \(C_4=1,\ C_5=14,\ C_6=145,\ C_7=1412\).

   |\(a\)|\(k\)|\(c\)|
   |---:|---:|---:|
   |194|6|40|
   |201|6|97.5|
   |220|6|143|
   |223|6|\(C_6\)|
   |256|7|\(C_7\)|
   |290|8|\(C_8\)|
   |325|9|\(C_9\)|
   |360|10|\(C_{10}\)|
   |396|11|\(C_{11}\)|
   |431|12|\(C_{12}\)|
   |467|13|\(C_{13}\)|
   |503|14|\(C_{14}\)|
   |547|15|\(C_{15}\)|
   |570|16|\(C_{16}/4\)|

   These compare at fixed onsets by the pointwise maximum and at fixed coefficients by the lowest proved onset; the proofs do not imply optimality. In particular any constant \(>1\) cannot persist on a full ray: the same barriers below and the decaying prime-counting error give \(G(L)\to1\). The inverse powers give genuine stronger whole-ray profiles despite this limit.

The stated source zero-margin rays are Dudek–Platt Theorem 1.2 (PDF p.2), \(L\ge9658\), and Platt–Trudgian Theorem 2 (PDF p.3), upper ray \(L\ge3915\) and a finite branch terminating at \(L=58\); see the endpoint correction below. The new inequalities close the original large open log interval, with positive margins there. When desired one may include any direct original \(\pi\) upper/lower envelope in the following product computation, e.g. PT Corollary 2 (PDF p.3) at \(L\ge2000\), or the Dusart \(\pi\) estimates of §5.1 on their domains, using their own li convention. The strongest lawful B0-vs-D01 comparison, including QRH-derived envelopes, is the implication in psi.md, not a comparison to only one stretched-exponential source branch.

## Derivation and reproducible variable profile

Use Dusart §5.1 (PDF pp.13–14) for the principal-value convention \(\operatorname{li}\). Put \(F(v)=v e^{-v}\operatorname{li}(e^v)\). For \(v\ge35\),
\[
 A_{16}(v)<F(v)<U(v),\qquad A_{16}(v)=\sum_{j=0}^{16}\frac{j!}{v^j},
 \quad U(v)=A_{16}(v)+3\,17!/v^{17}.
\]
Indeed \(y=e^{-v}\operatorname{li}(e^v)\) solves \(y'+y=1/v\). For \(A_{16}/v\) the residual is \(1/v-17!/v^{18}\); for \(U/v\) it is \(1/v+[3(1-18/v)-1]17!/v^{18}\), strictly above \(1/v\) for \(v\ge35\). Multiply a difference by \(e^v\) for ODE comparison. The initial bounds at 35 follow by summing \(\log 35+\sum_{j\ge1}35^j/(j\,j!)+C\), \(|C|\le1\), through \(j=200\) with tail \(<2\,35^{201}/201!\). To see the bound on \(C\), substitute \(t=e^w\) in li: the constant after removing \(\log v\) is the sum of \(\int_{-\infty}^{-1}e^w/w\,dw\) (between \(-1\) and 0) and \(\int_{-1}^0(e^w-1)/w\,dw\) (between 0 and 1). Symmetric deletions in \(t\) or \(w\) have the same PV limit, since the ratio of the deletion widths in \(w\) tends to 1.

Here are explicit majorants \(r_-(v),r_+(v)\) for the negative and positive sides of
\[
 r(v)=v e^{-v}\big(\pi(e^v)-\operatorname{li}(e^v)\big)
\]
for \(v\ge34\). Take the pointwise minimum of the following applicable bounds.

* **Finite branch \(34\le v\le58\).** Put \(B(v)=(v-2\log(v/(\pi e)))^2-4\), with \(\pi\) in constants denoting the circle constant. The bound is
  \[
  D_\pm(v)=\left[\frac{B(v)+1.84v}{8\pi}+b_\pm\right]e^{-v/2}
       +\left(2000+\frac{.08e^{17}}{4\pi}\right)v e^{-v},
       \qquad b_-=1.01,\quad b_+=-.9999.
  \]
  Use CH2 Corollary 9.3 (PDF p.36), stronger (9.4), with \(T(v)=2\pi^2e^{v/2}/v\); \(T\) is increasing here and its endpoints are between \(10^7\) and \(H\). Its original hypotheses hold. Convert to theta using the power corrections in psi.md: the upper power correction is less than \(1.01e^{-v/2}\) here and the lower is at least \(.9999e^{-v/2}\). For the signed partial summation integrals from 34 to \(v\), the absolute theta bound in the integrand is at most \(.92e^{v/2}/(8\pi)\) after dividing by \(v^2\) in log coordinates and multiplying by \(e^v\). Indeed \(2\log(v/(\pi e))>2.7\); using the weaker shift 2.7 it suffices that \(.08v^2-5.4v+2.7^2-4+8\pi(1.01)\le0\), increasing on this interval, verified at 58.
* **Plateau branch, \(v\ge34\).** With \(a=1.048\cdot10^{-12}\),
  \[
      C(v)=a(1+2/v)+115(1+3/v)e^{-v/2}+2000000 v e^{-v}.
  \]
  CH2 Corollary 1.3 (PDF p.3) and the power correction give theta relative error \(\le a+115e^{-v/2}\) for \(v\ge34\). The two exponentials \(e^t/t^2,e^{t/2}/t^2\) have log derivatives \(>1/2,>1/3\) respectively for \(t\ge34\).
* **QRH branch, \(v\ge100\).** The bound is
  \[
  D_Q(v)=(1+4/v)\,[q_\psi(v)+p(v)]+3\cdot10^{-16}v e^{100-v}.
  \]
  Each positive term in \(e^t(q_\psi(t)+p(t))/t^2\) has log derivative \(>1/4\) for \(t\ge100\). For the rational factor \(t/(t-92)\) use its log derivative \(-92/[t(t-92)]\); other terms are powers times exponentials. Start the convolution at 100. The contribution from below 100, scaled by \(e^{-100}\) before the factor \(v e^{100-v}\), is bounded by \(2a/100^2+345e^{-50}/100^2+2000000e^{-100}<3\cdot10^{-16}\).

These computations use, in unscaled \(x\) coordinates, the identity
\[
 \pi(x)-\operatorname{li}(x)
  =\frac{\theta(x)-x}{\log x}
   +\int_2^x\frac{\theta(t)-t}{t\log^2t}dt
   +\frac2{\log2}-\operatorname{li}(2).
\]
The absolute contribution from the integral up to 600 and the normalization constant is \(<2000\), using Dusart Theorem 4.2, \(k=0\), and \(598/\log^2 2+10<2000\). For \(600\le x\le e^{34}\) use finite RH Corollary 1 (Platt–Trudgian finite RH, PDF p.4) or PT Lemma 6 (PDF p.9), the **theta** estimate (not the potentially misprinted pi estimate). This gives the integral up to \(e^{34}\) bounded, with constants, by \(2000+e^{17}/(4\pi)<2000000\). The general convolution rule used above is \(\int_b^v f(t)dt\le f(v)/\lambda\) for \(f>0\) with \((\log f)'\ge\lambda>0\).

Also, Dudek–Platt proof of Lemma 3.2 (PDF p.8) explicitly supplies the finite fact \(\pi(x)<\operatorname{li}(x)\) up to \(1.2\cdot10^{17}\) where used there (also used in Dusart proof of Theorem 5.1). It is used here only for \(36.72\le L\le39.32\), and this branch sets \(r_+(L)=0\) there. Full RH is not used. The two-sided profiles in the table do not need this finite sign fact.

With the principal-value li main term, the normalized gap satisfies for \(L\ge36.72\)
\[
 G(L)> L^4\left[\frac{L}{L-1} A_{16}(L-1)-U(L)^2\right]-\mathcal E(L),
 \quad
 \mathcal E(L)=L^4\left[\frac{L}{L-1}r_-(L-1)+(2U(L)+r_+(L))r_+(L)\right].
\]
This follows by multiplying the lower bound at \(x/e\) by the positive prefactor and squaring the nonnegative upper bound at \(x\). It is strict from the li barriers. Use the sharper non-expanded rational expression as one variable profile. The poly certificate instead uses \(P(L)=\sum_{j=4}^{34}d_jL^{4-j}\) with
\[
 d_j=\sum_{i=0}^{\min(16,j)} i!\binom ji-\sum_{i+i'=j}u_i u_{i'},\quad
 (u_0,\ldots,u_{17})=(0!,\ldots,16!,3\cdot17!).
\]
Treat other \(u_i\) as zero. The omitted coefficients in \(L A_{16}(L-1)/(L-1)\) are positive, and subtraction of \(U^2\) is exact. \(d_0,\ldots,d_3=0,\ d_j=C_j\) for \(4\le j\le16\). Using \(P(L)-\mathcal E(L)\) gives another profile with no cancellation in its leading orders. These are all-domain formulas, not interpolated samples. Take the maximum with the constant and higher-order branches and with the zero bound where positivity is known.

## Finite certificates and analytic tail

For each finite log-cell \([\ell,u]\), all applicable chosen \(D_\pm,C,D_Q,U\) are decreasing over that cell. For \(D_\pm\), put \(g(v)=v-2\log(v/(\pi e))\); \(g\ge v-6\) and \(0<g'<1\) here. The coefficient of \(e^{-v/2}\) is positive and its derivative is less than half its value (the displayed formula gives this even with \(b_+=-.9999\)). The remaining functions are powers times decreasing exponentials and decreasing rational factors. Restrict to branches that hold throughout the cell; shift both endpoints for \(L-1\). Bound \(\mathcal E\) by evaluating its bracket at the left and \(L^4\) at the right. Compute the full interval of \(P\) by Horner in \([1/u,1/\ell]\), and subtract an upper enclosure of the tested profile. The strict check is on the full cell. This certifies the finite rows and \(1+14/L\) through \(L=192\), with both endpoints included.

For \(L\ge192\), \(D_Q(v)e^{v/8}\) is decreasing for \(v\ge L-1\), term by term. The code freezes it at \(a-1\) for each tail onset \(a\). The resulting upper bound for \(L^{k-4}\mathcal E(L)\) decreases on \(L\ge a\) since \(L^k e^{-(L-1)/8}\) does (\(a>8k\)); the other bracket factors may all be frozen at \(a\) or \(a-1\). For \(1+14/L\) use \(k=6,c=0,a=192\); for the other profiles test against \(C_k-c\). The unused polynomial remainder has nonnegative sign to the required degree: \(d_j=C_j>0\) for \(4\le j\le16\), and
\[
 d_n>\sum_{j>n,\ d_j<0}|d_j|a^{n-j}
\]
is certified at \((a,n)=(192,11),(201,15),(250,16)\). At \(a=300\) the analogous sum for \(n=16\) is less than \(C_{16}/2\), so one can retain half of degree sixteen after all later terms. For the exact order-\(k\) profiles, multiply the error by \(L^{k-4+1}\) and use the next Taylor coefficient (half for \(k=15\)); the rescaled error decreases because \(L^{k+1}e^{-(L-1)/8}\) does. For the three smaller coefficients of order six use the slack in order six and also one or two of the following positive terms, moving them to the right side and multiplying by \(L^{j-4}\) where \(j=7\) or 8. The right side is then a polynomial with nonnegative coefficients and hence increasing. At \(L=570\) the error multiplied by \(L^{12}\) is less than \(C_{16}/4\), retaining a quarter of degree sixteen. These are monotone analytic tails, not bounded grid extrapolations. The separate executable mode cert.py tails replays the sharpened checks.

The Python arithmetic uses dyadic intervals rounded outward by integer floors and ceilings. It evaluates exponentials by scaling the argument into \([0,1]\), using 26 Taylor terms plus tail \(2/27!\), raising to the integer scaling power, and reciprocating for negative arguments. Logs use scaling into \([1,2]\) and the series in \((z-1)/(z+1)\), with tail \(<3/3^{79}\) after the retained terms. Pi is enclosed by the alternating arctangent series and Machin's formula (obtainable by tangent addition). No machine floating output is used to decide any sign.

## The low real join and its trust tier

The finite integer coverage \(A<m\le 1.15\cdot10^{16}\) is the finite computation in Dudek–Platt (PDF pp.8–10, Lemma 3.4 and its preceding statement about the computation up to \(10^{11}\); also the finite branch announced by Platt–Trudgian Theorem 2). It does not use the RH-dependent analytic continuation in Dudek–Platt Lemma 3.2. Use just the finite **integer** conclusion, not the literal real onset of PT. Between \(m\) and \(m+1\) pi is constant and \(e x/\log x\) is increasing, while \(\pi(x/e)\) is nondecreasing. This extends the finite join, and \(e^{36.72}<1.15\cdot10^{16}\) so it overlaps the new analytic proof. The source finite interval has not been independently resieved; in particular the large stepping computation is relied on at literature trust, not asserted verified from source code. The displayed stepping proof in DP has endpoint strictness and real-step qualifications; the argument here does not use that text as a general real-valued stepping lemma.

Separately, the exact counts in cert.py give \(\pi(A)=1644673232\) and \(\pi(A/e)=632207037\). For clarity, the quotient sieve keeps \(s(y)=y-1\) initially for all distinct \(y=\lfloor n/j\rfloor\), and at prime \(q\) subtracts \(s(\lfloor y/q\rfloor)-s(q-1)\) for \(y\ge q^2\) in decreasing order. This deletes precisely the composites with least prime factor \(q\): their cofactor is \(\ge q\) with no smaller factor. The set of quotients is closed under \(y\mapsto\lfloor y/q\rfloor\) as needed and includes all integers through \(\lfloor\sqrt n\rfloor\), so primality of \(q\) is detected by \(s(q)-s(q-1)\). After \(q\le\sqrt n\), no composite remains. The certificate shows \(\lfloor x/e\rfloor=14111427770\) throughout \([A,A+1]\). On \([A,A+1)\) both counts are constant; the gap is strictly increasing there and the two rational offsets in the theorem give opposite signs. Thus the published inequality interpreted literally for all real \(A<x\le e^{58}\) is false, e.g. at \(A+.21792\). The corrected real endpoint follows, without any assumption on equality at a prime or at \(ep\).


There is also a local quantitative real profile all the way to the open low endpoint: for \(x_*<x<A+1\),
\[
 R(x)>\frac{e\,632207037\,(\log(A+1)-1)}{\log^2(A+1)}(x-x_*).
\]
Indeed \(e\,632207037\,(\log x-1)/\log^2x\) is strictly decreasing on this interval, so its value at \(A+1\) is a strict lower bound for the derivative throughout the integration. More generally the floor-interval monotonicity yields \(R(x)\ge R(m)+e\,\pi(m/e)[x/\log x-m/\log m]\) for \(m=\lfloor x\rfloor\) in the inherited finite interval, a computable profile if exact local counts are wanted. It is not a certified rounded uniform normalized coefficient across the finite range.

## Attempts and limitations

The naive absolute finite-RH pi error alone makes the lower profile negative near \(L=39\) and misses the earlier onset. Instead use the CH2 finite-height strength, signed prime-power subtraction, and the independent finite sign \(\pi(x)\le\operatorname{li}(x)\). The ODE barrier and exact polynomial cancellation avoid evaluating two nearly equal interval expressions over tiny cells. The CH2 absolute plateau cannot by itself maintain \(1+14/L\) on the entire ray, since its induced normalized perturbation grows like \(L^4\); the QRH density branch supplies the needed overlap and decay. For \(L<36.72\) we do not certify a uniform positive normalized coefficient across the entire finite region: the published integer positivity gives no quantitative margins there, and near \(x_*\) the gap tends to zero through positive values. A different verified finite computation would be needed to optimize those margins. The inspected finite and tail tradeoffs do not establish global optimality for any positive margin.
