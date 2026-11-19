# Common spectral estimate and comparison premises

## Premises and scope

B0 means all seven permitted originals, with their published hypotheses and inherited computation trust. B1 means B0 plus INPUT_CONTRACT.json (FOLLOWUP-D02): for **every real** $x\ge  e^{200}$, $|\psi (x)-x|\le  x^{27/32}(\log  x)^2/64$. Put $v=\log  x$, $E(v)=e^{-v}\psi (e^v)-1$, $H=3\cdot 10^{12}$. All summatory functions are right continuous. B0 and B1 are nested, never replacements for one another.

OpenAIQRH, original PDF p.4 Theorem 1.1, with its proof concluded on p.197, gives $\Re \rho\le 7/8$ for all nontrivial zeros of $\zeta $; it does not exclude equality. Under B1 we have instead $\Re \rho\le 27/32$. In fact for $\Re  s>1$, Euler product and integration by parts give
$$
-\frac {\zeta '(s)}{\zeta (s)}=\frac {s}{s-1}+s\int _1^\infty (\psi (t)-t)t^{-s-1}\,dt.
$$
The integral on $[1,e^{200}]$ is holomorphic; on $[e^{200},\infty )$ the exact contract gives locally normally convergent integrals (even after differentiation) for $\Re  s>27/32$. A zero would give a pole of the logarithmic derivative, which the continued expression does not have there. No boundary exclusion is claimed. This proves an earlier usable consequence than the starting point of the direct majorant; it does **not** apply that direct majorant below $e^{200}$. The constant $1/64$ and threshold are used as given in this argument, but the resulting zero boundary would follow with any finite coefficient and cutoff at the same power with this logarithmic factor. The direct branch $v^2e^{-5v/32}/64$ still enters minima where legal.

Platt--Trudgian FiniteRH, original PDF p.2 Thm 1, gives RH for $|\Im \rho |\le 3000175332800$, larger than $H$. Real zeros with $0<s<1$ are absent also by the alternating series for $(1-2^{1-s})\zeta (s)$ (strictly positive by pairing terms). Consequently all zeros in the high-real-part sums below have $|\Im \rho |>H$. Conjugate zeros are counted with multiplicity. The sources are used as stated, not re-proved by this packet.

## A finite, monotone majorant from density

FKS PDF p.7 $2.14$, Cor.2.9, and pp.26–27 Table 8 **first block, $a_1=0.77$** give for $t\ge  H$
$$
 N(s,t)\le  c_1 t^k(\log  t)^q+c_2(\log  t)^2,\qquad 
 k=\tfrac83(1-s),\quad  q=5-2s .
$$
Use the rows in cert.py (upward padded), on their stated $s$-intervals. Only $3/4\le  s<7/8$ is needed. FKS p.4 defines $N(s,t)$ with $\Re \rho\ge s$ and $0<\Im \rho<t$. We use its bound for the subset $\Re \rho>s$, and at closed ordinate endpoints use the right limit of the continuous majorant. Equalities at internal real-part cuts are assigned to the bin on their **left**. No bound from the prospective $0.618$ block is needed. With $h=\log  H, d=1-k$, let
$$
 J(h)=\sum _{j=0}^3 \binom{3}{j}h^{-j}
 \left (\frac {j!}{d^{j+1}}+\frac {(q-3)(j+1)!}{h d^{j+2}}\right ),
\quad 
 C(s)=2\left [c_1 H^{-d}h^q J(h)+c_2H^{-1}(h^2+2h+2)\right ].
$$
This bounds $2\sum _{\beta >s,\gamma >H}1/\gamma $. Partial summation passes to infinity since $k<1$. For the integral substitute $t=H e^z$, use $(1+z/h)^{q-3}\le 1+(q-3)z/h$, and integrate the polynomial times $e^{-dz}$. This removes the log-power loss on the capped zeros. The same proof bounds the tail $\gamma >T\ge  H$ with $H,h$ replaced by $T,\log  T$: the lower boundary contribution $-N(s,T)/T$ can be discarded.

For cap $b$ take cuts $s_0=3/4<s_1<\cdots <s_m<b$, the grid of spacing $1/2000$, and set $s_{m+1}=b$. At each cut take $C_j=\min _{i\le  j}C(s_i)$, using optionally outward rational rounding before the minimum (the executable uses this option). Put $C_{m+1}=0$ and
$$
 Z_b(v)=\sum _{j=0}^m (C_j-C_{j+1})e^{-(1-s_{j+1})v}.
$$
Indeed the total weighted exponential is at most
$$
 C_0 e^{-(1-s_1)v}+\sum _{j=1}^m C_j
 (e^{-(1-s_{j+1})v}-e^{-(1-s_j)v}).
$$
This follows by charging each bin its right endpoint and using the upper bounds on cumulative masses; expanding gives the displayed nonnegative exponential mixture. Thus $Z_b$ bounds the conjugate-pair-weighted high-zero sum with denominator $\gamma $, which bounds the same sum with $|\rho |$ or $|\rho -1|$. There is no factor of two left to insert. Truncating the grid at $27/32$ instead of $7/8$ makes $Z_b(v)$ strictly smaller for $v>0$ in this construction $(C_j>0)$; weight on subsequent increments has actually been removed. A finer grid, or taking the left limit of a density row when legitimate, gives further variants by the same proof. The displayed grid is the one used for the certificates.

## All-real explicit formula and absolute high spectral part

Use FKS PDF p.8 Theorem 3.2 with $(\alpha ,\omega ,M,\log  x_M)=(1/2,0,2.091,40)$, the **all-real** version stated there rather than the older contested half-odd-integer version discussed in FKS Remark 3.3. Set $T=e^{v/2}/6$. For (vge58), $51,v<T<(e^{v/2}-2)/5$; also $T^*\le 2.45T<e^{v/2}$. The fractional error is $\le 12.546v,e^{-v/2}$. For $\gamma \le  H$, Platt--Trudgian PNT PDF p.4 Lemma 2 gives $2\sum 1/\gamma <117$. For all $\gamma \le  T^*$ the same lemma at $e^{v/2}$ gives $2\sum 1/\gamma \le  v^2/25+2$ $use (8\pi>25)$. Zeros outside the RH block with $\beta\le 3/4$ therefore contribute at most the second part of
$$
 V(v)=(117+13v)e^{-v/2}+(v^2/25+2)e^{-v/4},\qquad 
 S_b(v)=V(v)+Z_b(v).
$$
In particular $|E(v)|\le  S_b(v)$ for every (vge58). CH2 PDF p.3 Cor.1.3 gives another convenient absolute envelope (J_{
m CH}$v$=0.000000000001047198+113.67e^{-v/2}), also for (|U|) in the Mertens proof.

For (vge62) there is a sharper **transport** than integrating the positive envelope $S_b$. Write $a=1-b$ and use
$$
 E(v)=-\sum _{\beta >3/4}\frac {e^{(\rho -1)v}}{\rho }+\mathcal  E_b(v),\qquad 
 |\mathcal  E_b(v)|\le  D_b(v):=V(v)+12v^4e^{-(a+1/6)v}+15v^2e^{-(a+1/2)v}.
 \tag {A}
$$
Indeed $T\ge  H$ there. Add the absolutely convergent high-zero tail to the truncated formula; bound the omitted part by the density integral at $s=3/4,T=e^{v/2}/6$, multiplied by $e^{-av}$. Here $q=7/2$, $d=1/3$, $J(\log  T)\le  J(h)<6$; $(\log  T)^q\le (v/2)^4$ and $T^{-1/3}=6^{1/3}e^{-v/6}$. The padded constants $12,15$ follow from
$2(7.798)6\cdot 6^{1/3}/16<12$ and
$12(4.101)(1/4+1/62+2/62^2)<15$.
These are checked in mertens.py. Dividing by large ordinates in subsequent integrations is the source of an additional gain, even in the original-input reconstruction. Tonelli/dominated convergence apply to the absolute high-zero majorant on (vge62), with integrable envelope $Z_b(v)$.

For $\theta $, always retain $0\le \psi (x)-\theta (x)<1.000000147\sqrt {x}+1.78x^{1/3}$ (Dusart2018 PDF p.13 Cor.4.5). For early finite work use Platt--Trudgian FiniteRH PDF p.4 Cor.1 and the PNT paper PDF p.9 Lemma 6; in particular $|\theta (x)-x|\le  \sqrt {x}(\log  x)^2/(8\pi)$ on $[600,e^{58}]$, and the same estimate for $\psi $ in the finite-RH range. CH2 PDF p.35 Lemma 9.2 gives $|\psi (x)-x|<0.791\sqrt {x}$ on $[10^4,10^{13}]$. We do not rely on deciphering or strengthening its weighted numerical display $9.1$.

## Cumulative envelope conventions

On any point where multiple supplied bounds are valid they may be intersected; for positive envelopes use their pointwise minimum, not a single fixed choice for the entire ray. In particular one may include in the $\psi $ seeds, on their stated domains, Dusart2018 Prop.3.2, Thm.3.3; Platt--Trudgian PNT Thm.1 with all Table 1 rows and Cor.1 for $\theta $; FKS Thms.1.1–1.2 (including admissible step and asymptotic table rows), Cor.1.4; CH2 Cor.1.2 with $10^7\le  T\le 3000175332800$ when $x>\max (T,10^9)$, CH2 Cor.9.3 on its admissible finite-height interval; and the two early finite-RH and CH2 branches above. For $\theta $ include all Dusart Thm.4.2 rows. For $\pi$ one can include the original inequalities directly, retaining each normalizing constant before comparing it to another. No unverified RH or outside paper is a separate premise. The named numerical benchmarks use the simpler checked sub-envelopes identified in each application; adjoining any valid original seed only improves the portfolio. The all-original reconstruction in this submission applies the **same new procedures** at $b=7/8$; it is not a blind baseline or a claim of optimality among all inferences from B0.
