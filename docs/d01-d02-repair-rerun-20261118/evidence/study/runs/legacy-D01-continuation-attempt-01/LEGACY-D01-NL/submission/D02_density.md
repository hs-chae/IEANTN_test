# Strongest tail candidates: remove both powers of the logarithm

The density estimate here is new to the study, not a verification of a source theorem. It improves both requested applications and the Chebyshev input. Use (eta_*=27/32) with PsiMajorant, or (eta_*=7/8) without it using the admitted OpenAIQRH Theorem 1.1. Let (k=1-eta_*).

## Zero-free region supplied by PsiMajorant

For (Re s>1), absolute convergence, unique factorization and partial summation give
[
 -rac{zeta'}{zeta}(s)=rac{s}{s-1}
      +sint_1^infty(psi(u)-u)u^{-s-1},du .
]
By the input and local boundedness the integral is holomorphic on (Re s>27/32) (locally uniform convergence including the differentiated integrals). The meromorphic continuation of (zeta) needed there already follows from
(zeta(s)=s/(s-1)-sint_1^infty{u}u^{-s-1}du) for (Re s>0), first verified by partial summation in the half-plane of convergence. The identity for its logarithmic derivative continues meromorphically, and a zero would give a pole other than 1. Thus every zeta zero in the critical strip has real part (le27/32). This assertion allows equality at the boundary. No additional hypotheses about zeros are used except the admitted finite verification as specified below.

## An exact decreasing error function

Let (H_0=3cdot10^{12}), (L=28.72<log H_0), (n=256), (sigma_i=3/4+(eta_*-3/4)i/n). For (3/4lesigmaleeta_*), put
[
 p=	frac83(1-sigma),quad q=5-2sigma,quad
 d(sigma)=
 rac{9.8,3^p L^q e^{-(1-p)L}}{1-p-q/L}
       +103,e^{-L}(L^2+2L+2).
]
Define
[
egin{split}
 c_0&=d(sigma_{n-1}),qquad c_i=d(sigma_{i-1})-d(sigma_i)quad(1le i<n),\
 C_{eta_*}(t)
 &=c_0+sum_{i=1}^{n-1} c_i e^{-(eta_*-sigma_i)t}
     +left(rac{t^2}{9cdot6.28}+1.8642
ight)e^{-(eta_*-3/4)t}
     +2.091, t,e^{-(eta_*-2/3)t},\
 F_{eta_*}(t)&=e^{-kt} C_{eta_*}(t).
end{split} 	ag{D}
]
All (c_i) are nonnegative, since the positive first summand in (d) decreases with (sigma) (its numerator decreases, denominator increases). Then for all real (xge e^{80}),
[
       |psi(x)-x|le x^{eta_*} C_{eta_*}(log x).
]
The function (C_{eta_*}) decreases on (tge80), including both polynomial-exponential terms, by differentiation. Some simpler uniform constants (use any row when (t) is at least its threshold):
 
| with PsiMajorant: (t_0) | upper constant | using QRH: (t_0) | upper constant |
|---:|---:|---:|---:|
| 169 | .270 | 187 | .014 |
| 200 | .227 | 200 | .013 |
| 300 | .177 | 300 | .0102 |
| 400 | .159 | 400 | .0092 |
| 1000 | .135 | 1000 | .0079 |

This is a *pure power* estimate. For example, for every (tge200) the conditional envelope is at most (0.227/(200^2/64)=0.0003632) times PsiMajorant, a strict improvement by a factor exceeding 2753. It also supplies error estimates below the contract's (exp(200)) onset. It is not a strengthening of the exponent (27/32); the improvement is the removal of the log-power and a concrete coefficient with domain.

### Derivation and application of the density input

Dusart Theorem 2.3 (section 2.2.2, printed p. 231/PDF p. 5), states the Ramaré bound for (Tge2000, sigmage.52), with positive ordinates up to (T) and (Re
hogesigma). Use (log(1+u)le u) to get
(N(sigma,T)le 4.9,3^p T^p(log T)^q+51.5(log T)^2).
Our (sigmage3/4>1/2) makes the finite-height RH below (H_0) applicable (PlattTrudgianFiniteRH Theorem 1). Partial summation and (N(sigma,T)/T	o0) give
[
 2sum_{Re
hogesigma, Im
ho>H_0}1/Im
ho
 le 2int_{H_0}^infty N(sigma,v)v^{-2},dv
 le d(sigma).
]
For the last step substitute (s=log v) and enlarge the integral to (sge L). Bound (s^qle L^q e^{q(s-L)/L}); (1-p-q/L>0) already at (sigma=3/4) and increases. The other integral is (103int_L^infty s^2 e^{-s}ds). All sums here count multiplicity.

For (tge80), apply FKS Thm. 3.2 with (T=e^{t/3}) and the parameters of qrh.md. The cutoff is (le2.45T). In the zero sum the part with real part (<3/4) contributes at most
((t^2/(9cdot6.28)+1.8642)e^{-t/4}) after normalization by (x), from the reciprocal-sum lemma of Platt–Trudgian and (log(2.45T/(2pi))in(0,t/3)). For the right-hand group, if (f(sigma)=e^{-(eta_*-sigma)t}), majorize by the increasing staircase with value (f(sigma_{i+1})) on each cell starting at (sigma_i). Its weighted sum is at most
(d(sigma_0)f(sigma_1)+sum_{i=1}^{n-1}d(sigma_i)(f(sigma_{i+1})-f(sigma_i))).
Telescoping gives exactly (c_0+sum c_i f(sigma_i)). This uses the cumulative density instead of pretending that differences of upper bounds bound individual bins. Factor out (e^{-kt}) and add the relative Perron remainder (2.091t e^{-t/3}). Formula (D) results. The crucial convergence is the density exponent (p<1); a naive all-zero reciprocal bound keeps an unnecessary ((log x)^2).

### Sharper continuous version and asymptotic coefficients

In (D) one may replace (c_0+sum c_i e^{-(eta_*-sigma_i)t}) by the smaller
[
 d(eta_*)+int_{3/4}^{eta_*}[-d'(sigma)] e^{-(eta_*-sigma)t},dsigma.
]
To see this directly, write (f(Re
ho)=f(3/4)+int_{3/4}^{Re
ho} f'(sigma),dsigma) and use the cumulative density bound under this positive integral; integration by parts produces the stated function, dominated by its staircase version. It is decreasing, with limit (d(eta_*)) by dominated convergence. On (3/4lesigmaleeta_*), the log derivative of the first term in (d(sigma)) is bounded in absolute value by
[
 	frac83(L+log 3)+2log L+
 rac{8/3+2/L}{1-2/3-(7/2)/L}<100.
]
Adding the positive constant does not increase the magnitude, so (d(sigma)le d(eta_*)e^{100(eta_*-sigma)}). The continuous high term is at most (d(eta_*)t/(t-100)) for (t>100), by integrating (f') or the derivative formula. At (tge50000), this and the other two terms yield the simpler coefficients **.119** (contract) and **.0068** (QRH), certified at the lower endpoint then by monotonicity. Using the better continuous function in the integrals for Mertens and in the short-interval length also remains valid.

## Stronger Ramanujan statements

In (1), (3), (4) of ramanujan.md use (D_*(s)=aexp[-k(s-s_*)_+]) with (s_*=169) for PsiMajorant and 187 for QRH. Keep the same (B=115.1). This majorizes the Chebyshev errors by the appropriate endpoint bounds above; the extra (	heta) correction is (le1.4262e^{-s/2}), absorbed by (B). The integral factor (4/3) used in (1) is still sufficient because (kle5/32). Denote this radius by (r_{eta_*}); (3) and (4) are fully explicit.

Both versions give (R(x)>0) for the **optimal** ray (x>X_*) in ramanujan.md. For both (tge49) implies (t^6R(x)/x^2>1+14/t). For (tge50) the stronger lower bounds are
[
 1+14/t+65/t^2quad(mathrm{PsiMajorant}),qquad
 1+14/t+16/t^2quad(mathrm{QRH without PsiMajorant}).
]
On the PsiMajorant ray (tge205), respectively QRH ray (tge235), the coefficient of (1/t^2) can be increased to 144. Retain the earlier (13/t) margin starting at (48.25) with the contract and (10.9/t) there without it. Formula (3) may of course be larger than these simple uniform margins. The analytic mesh in density.py is rational. To complete comparisons after the finite mesh, the terms in (t^2{cal E}_*(t)) decrease after the endpoint and sum to less than (1/2) there. The main expression after its first two terms exceeds (144.99/t^2) for (tge40), since the two negative coefficients together are less than (0.01/t^2) in size (directly from the two integers in cert.py). For the coefficient 145 the tail comparison uses \(t^3{\cal E}_*(t)<100\) from 300 onward and the main coefficient \(1412/t^3\) with negative terms totaling less than \(1/t^3\). With the exact root, no gap remains between lower and upper positivity intervals. The non-QRH/noncontract candidate of ramanujan.md remains available with fewer source premises.

## Strongest Mertens tail functions

Define the explicit integral (I_{eta_*}(t)=int_t^infty F_{eta_*}(s)ds).
For evaluation, each (c_i e^{-(1-sigma_i)s}) contributes (c_i e^{-(1-sigma_i)t}/(1-sigma_i)), (c_0 e^{-ks}) contributes (c_0 e^{-kt}/k), and the two polynomial-exponential terms in (F_{eta_*}) have exponents (1/4,1/3). The exact integrated last two terms are
[
 e^{-t/4}!left(rac{4t^2+32t+128}{9cdot6.28}+4cdot1.8642
ight)
       +2.091 e^{-t/3}(3t+9).
]
Use the identities of mertens.md, with the following radii for (tge80):
[
  H_{eta_*}=F_{eta_*}+I_{eta_*},qquad
  K_{eta_*}=rac{F_{eta_*}}{t}+
        int_t^infty F_{eta_*}(s)(s+1)/s^2,ds
    le F_{eta_*}/t+(t+1)I_{eta_*}/t^2.
]
The left definition for (K_{eta_*}) is an exact integral error function; the right is an elementary closed upper bound. Put (H_{eta_*},K_{eta_*}) in place of (H_A,K_A) in all signed statements of mertens.md. This proves the prime-sum and product outputs on every such (x) with the same (V(t)), with no exception at discontinuities. More simply, for any one of the coefficient rows (c) of this note and (tge t_0) the radii may use (H=c(1+1/k)e^{-kt}), (K=c e^{-kt}(1+(1+1/t)/k)/t). The analytic error component of the contract-powered Mertens bounds is reduced by the same factor (0.0003632) throughout (tge200) for the integral versions; positivity of the kernels in (1) proves this without a grid. This comparison is for the analytic component, not a spurious factor on the common prime-power spill. In this range the total bound is strictly smaller as well. For QRH the new radius is strictly smaller on the prior (tge258) ray: the coefficient (.013) there is less than (W(258)), and (W) is increasing. Below those rays the finite-plus-analytic noncontract candidate may be better; use pointwise minima. The selected Mertens candidates are thus that finite-plus-analytic candidate plus these two density tails (the earlier tail derivations are kept for audit).
