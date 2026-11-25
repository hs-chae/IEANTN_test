# Separate explicit-onset result (B + E)

**Statement.** Under ordinary RH and the named analytic source inputs below, for all real x in each indicated domain there is a prime strictly between x and x+c sqrt(x) log(x):

| reported c | domain |
|---|---|
| 0.851127044 | x >= 4 (unbounded) |
| 0.8 | 4 <= x <= exp(114) |
| 0.78 | 4 <= x <= exp(70) |
| 0.777 | 4 <= x <= exp(65) |

These statements do not assert an asymptotic coefficient 0.8 or any obstruction to achieving it by a different method. They use published analytic inputs and an independent written reduction/checker, not an RH-only Mathlib closure or program PV.

## Source inputs and convention

Blanquer Robles v2, Lemma 5 and Sec. 4.1 Eq. (15), for the piecewise affine real even window W supported in [-5,5], and inverse Fourier pair with the exponent +2 pi i uv. Use the Fap window in the local rational supplement (certificates/witness-ap.json; m=80, scale=10^12), not the window of that source's Theorem 3. Eq. (15) is the Mellin explicit formula, under RH, with von Mangoldt weights. The hypotheses are checked below; the source proof in 4.1 applies to this window by exactly the same piecewise affine strip decay/mollification, with no numerical threshold attached to (15) other than Y_->1. Also use the source's zero-count input (Sec. 4.2, CMS arXiv:1708.04122v2 Lemma 9, with the correction provenance in Sec. 4.2): |N_zeta(T)-Q(T)| <= .15 log T+3 for T>=e, Q(T)=T/(2 pi) log(T/(2 pi e))+7/8, and N_zeta(10)=0 with the root of Q in (9,10). Use Montgomery–Vaughan for modulus 1 as stated in Blanquer Robles Sec. 4.3, i.e. for an interval (u,u+s] of length s>1 at positive start, the upper bound 2s/log(s). No Iwaniec effective onset is inferred. Finally, for the range below exp(40) only, use Büthe, arXiv:1511.02032v2 Theorem 2 (1.6)–(1.7), ordinary theta including p=x, with its exact finite domain in the task source facts. This enrichment replaces the source's historical gap-computation bridge. No GRH, no Schoenfeld, no octic source package.

## Derivation above exp(40)

Test the four internal coefficients b=0.851127043, 0.799999, 0.779999, 0.776999 respectively. Each is positive and <=1. Put t=log x, z=b t/sqrt(x), d=log(1+z)/2, a=x exp(d), lambda=5d, Delta=d/(2 pi). The inner interval is (a exp(-d), a exp(d)] = (x,x+b sqrt(x)t]; all weights W(log(y/a)/d)/sqrt(y) are supported on [Y_-,Y_+]=[x exp(-4d),x exp(6d)]. These quantities and W obey all the strip/support hypotheses by Lemma 5: the window is continuous, compactly supported and piecewise linear, F and F' decay quadratically on fixed strips; multiplication by the modulation in 4.1 preserves the required decay. In particular Y_->1.

The following rational bounds hold for t>=40. The series check gives exp(20)>4*10^8. The functions t^j exp(-t/2) decrease for t>=40 and 0<=j<=3. Thus z<10^-7, d<5*10^-8, lambda<2.5*10^-7, t lambda<10^-5; exp(d/2)<1.000002, so d sqrt(a) <= 0.500001 b t. From log(1+z)>=z-z^2/2,
d sqrt(a) >= b t/2-10^-6 and log(1/d) <= t/2-log(b t/2)+10^-6 (use -log(1-z/2)<=z). The right-hand logarithm bound is positive.

Denote J=int_{|v|>1} W_+(v) dv, A0=sum of absolute node heights / m (both wings, including zero once), H=W_+(1)+sum of positive rises of consecutive positive-part node heights on [1,5]. V0=Var(W) and V1=Var(W'), with zero slopes outside support. The exact checks give (upper bounds)
J<.020372, A0<1.004, H<.114278, V0<1.405, V1<4.062, max|W|<.7.
Further ||F||_1 <= U=.781771946951 and 1.000001>F(0)>=F(0)-4J>D=.918513815592.

**New exterior estimate.** For a component of a positive level set in one wing, with image length s in y=a exp(dv), use a single interval of length max(s, sqrt(a)/10), enlarged by arbitrarily small epsilon if necessary to include either boundary. It stays at positive start (the support is near x). Taking the epsilon limit gives a prime count at most 2(s+sqrt(a)/10)/(log(a)/2-log 10). This bound uses the full component length rather than rounding up to an integer number of sqrt(a) blocks; even intervals far shorter than sqrt(a) use a denominator appropriate to their enlargement. Multiply by (log a+lambda)exp(lambda/2)/sqrt(a), a bound on log(p)/sqrt(p) within the support. The coefficient is at most
B0(t)=4(1+lambda/t)exp(lambda/2)/(1-2 log(10)/t).
Integrated level-set component count is H per wing: as levels vary, a component starts at the left endpoint or at an upward node segment, except at a finite set of levels, as in (17). The Jacobian is <=a d exp(lambda), so the exterior weighted sum, with a possible p=x included, is at most
(1/5) B0(t) H + B0(t) exp(lambda) d sqrt(a) J.
The log bound log(10)<2.303 and t lambda<10^-5 give (1+lambda/t)exp(3lambda/2)<=1+.001/t (use exp(u)<=1+2u on [0,1]). Hence B0(t)exp(lambda) <= 4+20.83/t by an exact rational test at t=40. Also B0(t)<4.525. This proves the exterior upper bound
4 d sqrt(a) J + .905 H + 10.416 b J.
The leading penalty is still 4, not a claimed smaller BT constant.

**Other losses.** Evenness gives pole term at least d sqrt(a) F(0) minus d sqrt(a)A0(cosh(lambda/2)-1); this loss is <10^-10 by cosh u-1<=u^2 for 0<=u<=1 and the bounds on lambda and t lambda. The last term of (15) in absolute value is at most d A0/[sqrt(Y_-)(Y_-^2-1)] <10^-10 since Y_->10^15. The change of variables is dy/y=d dv.

For prime powers p^k with k>=2, the number of integer kth powers in support is <=1+lambda sqrt(Y_+)<=1+3t (the difference of the roots follows by integrating y^(1/k)/k in log y over width 2lambda). The absolute weight per occurrence is <= (t+1)/(2 sqrt(x)) because log p <= (log Y_+)/2 and max|W| exp(2d)<1. There are at most 2(t+1) possible exponents since log 2>.69. Total loss is at most (t+1)^2(1+3t)exp(-t/2)<.001, by decreasing monomial terms and the rational test at t=40.

For zeros apply the Stieltjes derivation in Sec. 4.2 (start at Q's root, both boundary counts there zero). The density term is bounded above by ||F||_1 log(1/d)+int log_+(|u|)|F(u)| du. Integration by parts using |(|F|)'|<=|F'| yields a remainder at most
d [.30 g1+(3+.15 log(2 pi/d)) 2(10 pi A0+g1)],
where g1=(5 V1+2 V0)/(2 pi)<4 and 2(10 pi A0+g1)<72. This is <.0001: d log(2 pi/d) increases for 0<d<=5*10^-8, and log(2 pi/(5*10^-8))<20 follows from pi<22/7 and exp(20)>4*10^8. The logarithmic moment itself is <.025 by the separate rigorous grid described below.

In (15), the inner prime term is at most (.7 t/sqrt(x)) times its prime count since log y/sqrt(y) decreases for y>=x. Thus, after subtracting all losses, this count times .7 t/sqrt(x) is at least
M_b(t)=(b D-U)t/2+U log(b t/2)-.02611-.905*.114278-10.416 b*.020372.
Here .02611 covers .025+.0001+.001 and an allowance .000003 for the pole, trivial zeros, d sqrt(a) replacement (F(0)-4J <=1.000001) and log replacement (U<1). Both endpoint values of each bounded t-range are strictly positive by exact rational enclosures for log; M_b is concave. For the unbounded range b D>U and M_b is increasing, so only t=40 is needed. A prime in the half-open interval for b lies in the strict-open interval for the larger reported c.

## Logarithmic moment certificate

Let L=16384, h=m/L, and 1<=u<=160. Formula (4) gives F(u)=sinc^2(u/m) P(u/m)/m, and sinc^2(s)=(1-cos(2 pi s))/(2 pi^2 s^2) for s!=0. On the mesh u=k h, integer FFT bounds for P and cos give an upper bound on |F(u)|; phase reduction mod L is only for P and cos, not the denominator. Start at k=floor(1/h) and finish at u=160. Two integrations by parts as distributions applied to v^2 W show |F''(u)| <= (25 V1+20 V0+2 A0)/u^2 < 133/u^2. The chord on each [a,b] has absolute-value integral bound h times the average of its endpoint bounds, and the pointwise interpolation loss is <=133 h^2/(8 a^2). Multiply by an upper bound for log_+ on this cell, 0.694 times the least j>=0 with 2^j>=b. Extend the first cell to the left of 1 for an upper bound only. Add both half-lines and the analytic tail at 160, using 2g0=V1/(2 pi^2)<.207 and the identity int_R^infinity (log u)/u^2 du=(1+log R)/R. The resulting moment upper bound rounds up to .024744564556. Log enclosures use the positive atanh series with geometric remainder and binary range reduction. No sampled point is used as an unchecked continuum claim.

## Bridge to x=4

For 1423<=x<=exp(40), put y=x+0.776999 sqrt(x)log(x). By calculus log(x)/sqrt(x)<=2/e<1, so y<2x<=2*10^18<10^19. The Büthe domain includes both arguments. Subtract theta bounds to get theta(y)-theta(x)>y-x-1.95 sqrt(y)+.05 sqrt(x)>0 since log(x)>7 and 1.95 sqrt(2)<2.8. This gives a prime in (x,y] and hence in any of the reported strict intervals. On 4<=x<=1423, the rational checker enumerates each integer floor k and the first prime p>k by trial division. It proves (0.776999)^2 k log(k)^2>(p-k)^2 using lower log bounds. Every real x in [k,k+1) has the same next prime p, and x+c sqrt(x)log(x) is increasing, proving the bridge on the full real continuum. Coefficients below 4/(sqrt(7)log(7)) cannot work with strict endpoints from x=4, because at x=7 the next prime is 11.

## Reproduction

In /work/submission run:
    /usr/bin/python3.10 explicit_cert.py /corpus/literature/Blanquer_supplement/certificates/witness-ap.json fft

Use the fft argument to rerun the mass certificate, not merely the other arithmetic. Inputs are from the mounted supplement and already byte-pinned by its SHA256SUMS. Stdout is not a source-first proof: the checker and the analytic estimates above are the independent E-tier derivation, and the identified source inputs remain B.
