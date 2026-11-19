# D02, the zero strip, and two direct weighted transfers

Let (B_0) denote all common originals at their original trust. Put
(t=log x, E(t)=e^{-t}psi(e^t)-1, H=3cdot10^{12}, h=log H).
In each of the following simultaneous constructions let
[
  b=7/8quad(B_0),qquad b=27/32quad(B_0+mathrm{D02}),qquad
  alpha=1-b.
]
These labels are for the assumptions used to obtain (Re
hole b).
The same algorithms, including density rows and integration, are used
in the two columns. D01 is already implied by (B_0) (see
`density.md`); it is also directly implied by D02.

## From the exact D02 input to a global spectral restriction

For (Re s>1), the absolutely convergent Euler product, and
integration of the step function (psi), give
[
 -zeta'(s)/zeta(s)=s/(s-1)+sint_1^infty(psi(y)-y)y^{-s-1},dy .
]
Indeed (int_n^infty y^{-s-1}dy=n^{-s}/s), and the first
logarithmic derivative follows from unique factorization by
differentiation in the absolutely convergent half-plane.
The integral over ([1,e^{200}]) is entire. For the rest, D02
bounds the integrand in absolute value by (rac1{64}y^{b-Re s-1}
(log y)^2). This gives locally uniform integration, also after any
number of derivatives, on (Re s>b). Uniqueness of meromorphic
continuation and the nonzero residue at a zero of (zeta)
therefore exclude such a zero in that open half-plane. The boundary
line remains allowed. This deduction uses the *given* exponent
27/32 and the entire tail but needs neither the numerical coefficient
nor the precise finite start. It does not assume a stronger QRH
statement for other (L)-functions. The original (b=7/8) is
OpenAIQRH Theorem 1.1 (PDF p.4); the continuation mechanism there
concerns a supremum over a family of Hecke characters, not just
(zeta) (Equation (12.1), PDF p.85; Proposition 20.3 and conclusion
on PDF pp.195–197). Substitution of (27/32) as that family
supremum, or as the target boundary of its existing estimates, is
not justified.

## High strip and a small residual; no variable-cutoff integration needed

Take (s_0=.75). Write (A(s)=1-rac83(1-s)) and (q(s)=5-2s).
For each closed density band from `.75-.80` through `.87-.88` use
the first subtable in FKS Table 8 (PDF p.26), Corollary 2.9 (PDF pp.7–8,
(2.17)), with constants rounded upwards in `d02.py:rows`. Thus
(N(s,Y)le cY^{1-A(s)}(log Y)^{q(s)}+d(log Y)^2) for (Yge H)
and (s) in that band. We use the asserted corollary and tabulated
bounds at published trust, not the alternative rows conditional
on the 0.618 constant in Remark 1.5. In particular this is not
a reoptimization using external sources for Theorem 2.7.
There are no zeros with (Re
hoge s_0), (|Im
ho|le H)
by FiniteRH Theorem 1 (PDF p.2) and the elementary no-real-zero
argument of `density.md`. Count multiplicities throughout.
For (Y=e^vge H) and (A(s)>q(s)/v),
[
 2sum_{substack{etage s\gamma>Y}}gamma^{-1}
 le B(s,v;c,d)
 :=2left[rac{c,v^{q(s)}e^{-A(s)v}}{A(s)-q(s)/v}
              +d(v^2+2v+2)e^{-v}
ight].
 	ag{1}
]
Use (int_Y^infty(N(s,y)-N(s,Y+))/y^2,dy) for the tail
and bound by (int_Y^infty N(s,y)/y^2,dy).
If a cut coincides with an ordinate, single ordinates do not
affect the integral; inclusion at the cut also works with
(int_Y^infty N(s,y)/y^2,dy) as upper bound.
For the first integral use ((v+w)^qle v^q e^{qw/v});
for the (d) term integrate exactly. This proves absolute
convergence of the high-strip sums even at infinite height.

Define the real-valued function
[
  E_h(t)=-sum_{etage .75}rac{e^{(
ho-1)t}}{
ho}.
]
Conjugate zeros are paired, and the sum is absolute; this is a
piece of a truncated explicit formula extended by an absolutely
convergent sum, not an assertion of absolute convergence for the
usual full explicit formula. The scaled total of the absolute
terms (also with (1/|gamma|) in place of (1/|
ho|)) is
nonincreasing in (t), since (etale b).
The following two bounds, each unscaled by multiplication by
(e^{-alpha t}), are used for that total.

* If (sin[l,r]) lies in a single density band, the first term
of (B(s,h;c,d)) has negative logarithmic derivative of magnitude
at most
[
 D_l=	frac83h+2log h+rac{8/3+2/h}{A(l)-q(l)/h}.
]
The second term is constant in (s). On that band use a rational
upper (D_l^+) rounded upwards to hundredths and
(B(s,h;c,d)le B(r,h;c,d)e^{D_l^+(r-s)}).
Write (e^{(eta-b)t}=e^{(s_0-b)t}+tint_{s_0}^{eta}
e^{(s-b)t},ds), apply (1), and integrate on each band, cutting
the last band at (b). The resulting bound (K_b^{
m loc}(t))
is the initial term (B(s_0,h;c_0,d_0)e^{(s_0-b)t}) plus
[
 sum_{[l,r]} B(r,h;c,d)rac{t}{t-D_l^+}e^{-(b-r)t}
                  ig(1-e^{-(t-D_l^+)(r-l)}ig). 	ag{2}
]
At boundaries the integral is insensitive to a singleton; the
initial value uses the first band. Finite numerical checks give
(D_{.75}<97,D_{.80}<92).
* A coarser comparison, useful even without the band subdivision:
apply the same layer identity separately to (.75leeta<.80)
and (.80leetale b), with the uniform maxima of the table
constants on the respective bands. Bounding the finite exponential
integral by the rational factor (t/(t-D)) including the boundary
term gives the sum
[
 K_b^{
m old}(t)
 = k_brac{t}{t-92}+6.12,rac{t}{t-97}e^{-(b-.80)t},
 qquad k_{7/8}=.0106,quad k_{27/32}=.149. 	ag{3}
]
For the upper bands use ((11.076,3.693)) or ((9.747,3.693));
for the lower use ((7.798,4.101)). The stated endpoint (B)-caps
are checked by the executable. This overcounts rather than
undercounts where the lower band uses a cumulative count.

Let (K_b=min(K_b^{
m loc},K_b^{
m old})) for (tge150); either
may be frozen at (t=a) in the *scaled* bound for every (tge a).
No monotonicity of (2) as a computed expression is assumed.

Use FKS Theorem 3.2 (PDF p.8, specifically the admissible tuple
((40,1/2,0,2.091))) with (T=e^{t/3}), and (T^*in[T,2.45T]).
The admissibility inequalities (max(51,t)<T<(e^{t/2}-2)/5)
already hold at 40 and persist by differentiation. For (tge150),
(T>H). Use Platt–Trudgian 2021 Lemma 2 (PDF p.4), including both
signs, with (log(T^*/2pi)<t/3), to bound the whole low strip
(eta<.75), and (1) with (v=t/3) to restore to the formula
the omitted high-strip zeros. Subdivide the density bands further
into pieces ([s,z]) of length (le .01) and cut at (b);
overcount any shared boundaries. The result is
[
 |E(t)-E_h(t)|le e^{-alpha t}sum_i r_i(t), qquad
 {r_i(t)}=
 left{
 (.017684t^2+1.865)e^{-(b-.75)t},
  2.091t e^{-(1/3-alpha)t},
  e^{-(b-z)t} B(s,t/3;c,d) 	ext{for each piece}
 
ight}.
 	ag{4}
]
Split the last (B) into its two summands for the computations.
The high-strip tail uses (1) at (T), not (T^*); in each piece
we bound (e^{(eta-b)t}) by its value at (z).
Importantly, (T^*) need not be the same at different (x).
We integrate the absolutely convergent (E_h), and bound (4)
separately. FKS 3.2 holds at real (x), including prime powers.
There is no extrapolation of a half-odd-integer formula to jumps.
No logical use is made of the earlier formula questioned by
FKS Remark 3.3.

For any summand in (4) write (r_i(t)=p_i(t)e^{-delta_i t}).
Then on (uge tge150),
[
 r_i(u)le r_i(t)e^{-lambda_i(t)(u-t)},qquad
 lambda_i(t)=delta_i-rac{7}{2t}>0. 	ag{5}
]
Indeed each positive polynomial factor has logarithmic derivative
(le 2/u), and (v^q/(A-q/v)) has logarithmic derivative in (u)
(le q/ule (7/2)/u); its denominator is positive at all these
(v). The exponents (delta_i) are respectively (b-.75),
(1/3-alpha), (b-z+A(s)/3) and (b-z+1/3).
In particular (delta_ige .09375) for both (b), by the
band endpoints and (A(.75)=1/3).
Thus the (r_i) decrease; (5) justifies all infinite joins.

## Mertens with the oscillating term still in the integral

Use (F,U,S,W,Z,J_j,J_{1,c}) and their exact constants as in
`mertens.md`. In (F) use the transformation
(E(t)-int_t^infty E(u),du); in (U) use
(E(t)/t-int_t^infty E(u)(u^{-1}+u^{-2}),du).
For the high strip every integrated zero gains (1/H) after
taking absolute values: for (F), integrate (e^{(
ho-1)u})
exactly; for (U), use
[
 1/u+1/u^2=int_0^infty(1+w)e^{-wu},dw,qquad
 |1+w-
ho|ge|Im
ho|>H.
]
Tonelli on absolute values against (e^{-alpha u}) proves
interchange, using (1). Thus the integral is bounded by the
same high-strip sum at (t) times (1/H) or
((1/t+1/t^2)/H), respectively. Taking absolute values
*before* the (u)-integral would instead lose a factor
approximately (1+1/alpha), even with the same zero-free line.

Putting (j=0,1), (d_0(t)=1, d_1(t)=1+1/t), define
[
 B_j(t;b)=K_b(t)(1+d_j(t)/H)
       +sum_i r_i(t)left(1+rac{d_j(t)}{alpha+lambda_i(t)}
ight).
 	ag{6}
]
Then (|F|le e^{-alpha t}B_0(t;b)) and
(|U|le e^{-alpha t}B_1(t;b)/t). Here (B_0(t;b)) is a
function, distinct from the premise label (B_0).
One may use (6) pointwise. For onsets (age150), each (B_j(a;b))
is valid after the same rescaling on *all* (tge a):
freeze the scaled high strip at (a), and use (5) and monotonicity
of (d_j,lambda_i). This argument covers the local bound (2)
without asserting that the capped expression (6) itself decreases.
For (W,S,Z) add their respective signed prime-power intervals
in `mertens.md`. For simple symmetric caps use
[
 p_b(t)=1.001e^{-(b-1/2)t}+2.67e^{-(b-1/3)t}.
]
It bounds the scaled error additions for (W), and for (tS,tZ).
For either product apply (e^v-1le v/(1-v)) to
(v=e^{-alpha t}(B_1+p_b)/t). Consequently the common constant
[
 C_M(a;b)=rac{B_1(a;b)+p_b(a)}
               {1-e^{-alpha a}(B_1(a;b)+p_b(a))/a} 	ag{7}
]
works for all four errors, with factor (e^{-alpha t}) for (W)
and (e^{-alpha t}/t) for the other three. Equations (6)–(7)
are implemented in `mcap` and `mnew.py`. The denominator is
positive by the endpoint checks (or use (3) and (4) frozen at
150 to bound it for larger (a)). For log-power shapes multiply
(7) by (a^2 e^{-alpha a}), whose continuation (t^2e^{-alpha t})
decreases on these rays. Non-strict for the exact expressions;
strict for the rounded upper caps checked with slack.

D02 alone, with the common normalization and prime powers but
without the density calculation, would replace the two caps on
(|F|,|U|) by
[
 rac{e^{-alpha t}}{64}
 egin{cases}
 (1+1/alpha)t^2+2t/alpha^2+2/alpha^3,\
 (1+1/alpha)t+1/alpha+1/alpha^2 ,
 end{cases}
 qquad tge200,quadalpha=5/32.
]
These follow by elementary integration of (u^2) or of (u+1).
They give a fallback faster exponent but fail to remove the
two logarithmic losses. The spectral calculation is what moves
the effective start before 200 and beats these caps uniformly
on their common ray.

## Prime counting and the shifted Ramanujan gap

By Dusart Corollary 4.5 (PDF p.13) and (4), a scaled (	heta)
error cap, frozen at any log anchor (age150), is
[
 C_	heta(a;b)=K_b(a)+sum_i r_i(a)
 +1.000000147 e^{-(b-1/2)a}+1.78e^{-(b-1/3)a}.
]
At the anchor let (V_*(a)) be the smaller of the two inherited
directional error bounds **only when both are symmetric there**.
All anchors here are (ge150), so `w(a,side)` is symmetric
(`v2`, possibly intersected with `v3,v4`). The Abel identity
and differentiating (e^{bt}/t^2), as in `ramanujan.md`,
give the following valid symmetric cap for
(|t e^{-t}(pi(e^t)-operatorname{li}(e^t))|):
[
 V_a(t;b)= C_	heta(a;b)left(1+rac1{(b-2/a)t}
ight)e^{-alpha t}
   + ig(V_*(a)+ C_	heta(a;b)e^{-alpha a}ig)rac{t}{a}e^{a-t},
 qquad tge a. 	ag{8}
]
Take the minimum over the available anchors in `d02.py` and
intersect separately with the older directional bounds on their
true domains. The earlier anchor is *not* an assertion of the
D02 input before (e^{200}). It uses the global spectral
consequence plus the FKS and finite RH estimates.

Write (f(t)=e^{-t}operatorname{li}(e^t)),
(mathcal L(t)=t^6(f(t-1)/t-f(t)^2)).
For one-sided caps (V_-(t),V_+(t)) on the scaled negative and
positive counting errors we have, at (tge151),
[
 G(t)ge mathcal L(t)-t^4left[
 rac{t}{t-1}V_-(t-1)+ V_+(t)ig(2tf(t)+V_+(t)ig)
ight].
 	ag{9}
]
As an alternative using a symmetric (V), one has the same
quantity as an upper bound on (|G-mathcal L|) after replacing
(V_pm) by (V). This is the exact expansion of the shifted
linear term and the square. For a strict polynomial lower bound,
(f(t-1)>S_{48}(t-1)), (f(t)<U_{48}(t)),
as follows from the certified anchor (110) and integrating
(f'+f=1/t). Here (S_N=sum_{j=0}^N j!/t^{j+1}) and
(U_{48}=S_{48}+2cdot49!/t^{50}). At the anchor the convergent
(operatorname{Ei}) series is used as in the inherited proof,
now through term 440; differentiate the upper barrier,
whose residual is ((49!/t^{50})(1-100/t)>0).
At (tge110), (t U_{48}(t)<1.01) by the anchor and
monotonicity of the positive inverse powers. Retain the lower
positive shifted-series coefficients through degree 100,
subtract the entire upper square, and use (2.02) in the error.
That polynomial is `P` in the source. No numerical difference
of (operatorname{Li}) values at huge (x) is required.
The errors at (t-1) and (t) always have their own onset checks.

An exact cell proof subtracts the target polynomial, multiplies
by (t^k) where chosen, and bounds each signed monomial by
its smaller endpoint. Each (V_a) decreases in its domain.
On a cell use only the anchors valid at the left endpoint of
the respective argument; additional anchors inside that cell
can only improve the bound. Cut at changes of other branches.
For a tail starting at (A), replace (t/(t-1)) by (A/(A-1));
(t^{k+4}V_a(t)) and the shifted (t^{k+4}V_a(t-1)) decrease
from (A>1+(k+5)/alpha), termwise using (8).
When taking the min one may freeze the anchor availability at
the left endpoint and minimize the whole-ray bounds; the
comparison at (A) is therefore sufficient. The quadratic term
uses (V(t)) decreasing as well. Residual positive terms with
(j>k) in (t^{k}(P-mathrm{target})) can be dropped, and
negative ones evaluated at the left endpoint; for (j<k) only
nonnegative coefficients are accepted in this tail shortcut.
When this shortcut is too costly, bisection covers the finite
prefix and joins to a later tail. See `claims.py`; unstated
provisional candidates do not form part of the portfolio.


### Direct-premise fallbacks (no use of FKS density)

The direct (F,U) formula above, plus (PP) and the same product
conversion, gives the rounded coefficient (.123) for
(t^2e^{-5t/32}) ((|W|)) or (t e^{-5t/32}) (the other
three errors), (tge200). For the ray proof freeze the
rescaled terms at 200, since the extra inverse powers, prime-power
ratios, and factor in the exponential conversion all decrease.

For a counting fallback, let (C=.015626, a=200, b=27/32).
From the input and Dusart 4.5, (|e^{-t}	heta(e^t)-1|le
Ct^2e^{-5t/32}) there, by checking the normalized extra terms
at 200. Bound the scaled anchor constant as in (8) using
(v_2(a)+Ca^2e^{-5a/32}). Now the Abel integral itself gives
the simple cap
[
 C(t^2+t/b)e^{-(1-b)t}
 + (v_2(a)+Ca^2 e^{-(1-b)a}),rac{t}{a}e^{a-t}.
]
The rescaled counting cap (V/(t^2 e^{-(1-b)t})) decreases;
at 220 it is (<.0158). Hence at (tge221), using the shifted
factor (t/(t-1)) in (9) together with ((t-1)^2/t^2)
and (tf(t)<1.01), one obtains
(|G(t)-mathcal L(t)|<.051t^6 e^{-5t/32}).
These density-free fallbacks are weaker than the main
claims where the FKS density input is retained.
