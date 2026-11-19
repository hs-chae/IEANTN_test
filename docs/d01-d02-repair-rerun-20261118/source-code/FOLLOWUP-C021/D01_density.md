# Strengthening the Chebyshev input

Let H be the input PsiMajorant. It implies every nontrivial zero rho has
Re(rho)<=7/8: for Re(s)>1 the absolutely convergent Euler product gives
-zeta'/zeta(s)=s/(s-1)+s integral_1^infty (psi(t)-t)t^(-s-1)dt.
The remainder is holomorphic on Re(s)>7/8 by H, locally uniform with its
derivatives. Analytic continuation (FKS §2, PDF p.4) and the nonzero principal
part at any zero prove the claim. Alternatively the exact strip assertion is
a literal conclusion of OpenAIQRH Theorem 1.1, PDF p.4 (not full RH).

Work in the strip S given by that conclusion. Write L=log(x), H0=3*10^12,
a=log H0. For L>=185 the bound is
|psi(x)-x| <= x^(7/8) D(L),
D(L)=0.0106 L/(L-92)+651 exp(-3L/40)+0.05 L^2 exp(-L/8)
          +12.546 L exp(-3L/8).
Use FKS Theorem 3.2 (PDF p.8) with T=sqrt(x)/6, alpha=1/2, omega=0,
M=2.091, giving last term with cutoff V=Tstar<=2.45T. Its hypotheses
hold also for real x. Real zeta zeros in (0,1) are absent: the alternating
Dirichlet series equals (1-2^(1-s))zeta(s) by continuation and is positive
there from pairing adjacent terms. Conjugation explains factors of 2 below.

For sigma>=.75 let S(sigma)= sum over beta>=sigma of 1/|gamma|.
By finite RH (Platt–Trudgian FiniteRH Thm 1), no zeros counted below H0.
Use the *stated Corollary 2.9* and Table 8 of FKS (PDF pp.7,26), not a
fresh optimization of Thm 2.7. For sigma=.75 take c1=7.8,c2=4.11; on
[.8,.875] use uniform inflated coefficients c1=11.08,c2=3.70. Then with
p=(8/3)(1-sigma), q=5-2sigma,
S(sigma) <= 2 c1 H0^(p-1) a^q/(1-p-q/a) + 2c2(a^2+2a+2)/H0.
Indeed 1/|gamma| is the integral of t^(-2) above |gamma|; for t=H0 exp(v),
(a+v)^q <= a^q exp(qv/a). All denominators are positive in these uses.
For sigma=.75 this is <651. At sigma=.875 the same expression using the
uniform coefficients is <.0106. The logarithmic derivative of its first
term with respect to d=.875-sigma is at most
(8/3)a+2log(a)+(8/3+2/a)/(1-p(.8)-q(.8)/a) < 92.
The constant second term can only help. Hence S(s)<=.0106 exp(92d).
For beta>=.8 apply the identity x^beta=x^.8+L integral_.8^beta x^u du
and this reciprocal bound; the answer is at most .0106 x^(7/8)L/(L-92).
For .75<=beta<.8 use 651 x^.8. For beta<.75 use
2(S0+B1(100,V+1)) < .05 L^2 by FKS Lemma 2.1, Remark 2.2 and
Corollary 2.3/Table 1 (PDF pp.4–5), with Rosser constants; V+1<sqrt(x). The scalar comparisons are verified by check.py.
Every summand of D is decreasing on this ray; D(185)<.022 and
D(200)<.020. Thus on the entire input ray the improved coefficient
relative to H is at most .020/(200^2/64)=1/31250, and the
asymptotic coefficient limit in the new envelope is .0106.

This use separates the source's literal Tab.8 from the conspicuous
delta-format discrepancy in Thm 2.7/Table 8 (do not infer raw parameters).


## Density-free fallback under S

For every real L=log x>=185,
  |psi(x)-x| < x^(7/8) [2+.322 w(w/2+1)+(2.091/64)L]
                  < .0045 x^(7/8) L^2,
  w=L/8+log 158.
Use FKS Theorem 3.2 with T=64*x^(1/8). Its `max(51,log x)<T`
and `T<(sqrt x-2)/5` hold at the anchor L=185 and persist:
e^(L/8)/L increases there and
[(e^(L/2)-2)/5]/e^(L/8) increases. The zero cutoff V<=2.45 T
has log(V+1)<w, so apply the same reciprocal-ordinate bound
2(S0+B1(100,V+1))<2+.322 w(w/2+1). The strip bounds all
numerators by x^(7/8); the error is (2.091/64)L*x^(7/8).
Divide by L^2: the resulting positive polynomial in 1/L
is decreasing, and check.py proves the upper coefficient
.0045 at the anchor. No density tables or reoptimization of
their printed parameters are required. On the whole input
ray this improves 1/64 by a factor >3.47, independently of
the much stronger density option. The Ramanujan unit/endpoint
and Mertens baseline gains can use this fallback under S.
