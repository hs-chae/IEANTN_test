# Explicit Chebyshev profiles used in both applications

Let b=7/8 and k=1-b. OpenAIQRH Theorem 1.1 (pinned version, PDF p.4) gives Re rho <= b; equality is allowed. H gives the same strip since for Re s>1
  -zeta'/zeta(s) = s/(s-1) + s integral_1^infty (psi(u)-u) u^(-s-1) du.
The remainder extends holomorphically to Re s>b by absolute local uniform convergence (including differentiated integrals); for continuation of zeta itself one can use s/(s-1)-s integral_1^infty {u}u^(-s-1)du on Re s>0. A zero in the open region would give a pole in the logarithmic derivative. No strict bound at b follows. The same proof can be parameterized by b=27/32 only with a different, stronger premise; that parameter is used in the explicitly separate sensitivity audit.

## Removing log powers with a tighter density integration

Set H0=3000175332800, the exact height in Platt–Trudgian FiniteRH Theorem 1 (PDF p.2), A=log H0. For 3/4 <= sigma <= b put p=(8/3)(1-sigma), q=5-2sigma, and z=1-p. Define

    d(sigma) = 9.8 * 3^p * exp(-z*A) * A^q / z
                   * sum_{j=0}^4 (q)_j/(z*A)^j
               + 103*(A^2+2*A+2)/H0,

where (q)_j=q(q-1)...(q-j+1) and (q)_0=1. This is decreasing in sigma: A>1, z increases, p,q decrease, with all factors positive and monotone in the indicated direction. Dusart2018 Thm 2.3 (PDF p.5, §2.2.2) and log(1+u)<=u give N(sigma,T)<=4.9*3^p*T^p*(log T)^q+51.5*(log T)^2, counting positive ordinates. Finite RH removes all such zeros through H0. Thus twice the reciprocal mass over the remaining ordinates is at most 2 integral_H0^infty N(sigma,T)/T^2 dT by nonnegative summation. For strict N conventions use sigma-epsilon and continuity as epsilon decreases to zero (the density premise applies in a neighborhood on the left). After substituting log T=A+v, bound (A+v)^q by its Taylor polynomial in v of degree 4: the fifth derivative is nonpositive for 3<q<4, on the entire v>=0 ray. Integrating each monomial gives exactly d(sigma). This does not require FKS Table 8 or optimization of its printed parameters.

For t>=80 set sigma_i=3/4+i/4096, i=0,...,m with sigma_m=b. Define the high-zero part in relative x-scale as either of

    F_step(t)=d(sigma_0)e^(-(1-sigma_1)t)
        + sum_{i=1}^{m-1} d(sigma_i) [e^(-(1-sigma_(i+1))t)-e^(-(1-sigma_i)t)];
    F_cont(t)=d(3/4)e^(-t/4)+t integral_{3/4}^b d(s)e^(-(1-s)t) ds.

These follow by majorizing the positive increasing test function exp(-(1-sigma)t) by its upper step function, or by integrating its positive derivative against cumulative mass. F_cont<=F_step: integrate over each cell and use the monotonicity of d. The step version is a sum of positive exponentials after telescoping; see coeff() in power.py. The grid is the same for both values of b, so the 27/32 step bound is strictly below the 7/8 step bound, not merely smaller at sample points. The same strict comparison holds for their continuous versions because the extra integral has positive measure and positive integrand.

Apply FKS Theorem 3.2 (PDF p.8; not the older Perron formula questioned in Remark 3.3) with T=e^(t/3), (log x_M,alpha,omega,M)=(40,1/2,0,2.091). The height conditions hold at 80, and thereafter T/t increases and (e^(t/2)-2)e^(-t/3) increases. Its cutoff is at most 2.45T. Platt–Trudgian 2021 Lemma 2 (PDF p.4) bounds twice the reciprocal sum up to 2.45T by (t/3)^2/6.28+1.8642: the log of (2.45T/(2*pi)) is between 0 and t/3. The contribution with beta<3/4 to the normalized error is thus bounded by this times e^(-t/4). There are no real zeros in the critical strip, since the alternating zeta series is positive on real 0<s<1 by pairing terms and equals (1-2^(1-s))*zeta(s) there by continuation. Conjugation gives the factor 2 for positive ordinates. Use |rho|>=|Im rho| for the complex terms. Hence the error bound for every real x=e^t, t>=80, is

    |psi(x)-x|/x <= F_b(t)
       = F_step(t) + [t^2/(9*6.28)+1.8642] e^(-t/4) + 2.091*t*e^(-t/3).

Take the minimum with the continuous version, or other available estimates, when useful. Multiplying by e^(kt) defines C_b(t). It decreases on t>=80: for the high step part this follows from positive exponential terms, for continuous from integration by parts (d(b)+integral_{3/4}^b (-d'(s))e^(-(b-s)t)ds). The polynomial-exponential remainders also decrease on this ray. An optional explicit bound for the continuous high part at t>140 is d(b)*t/(t-140) in C_b scale. Indeed the magnitude of the logarithmic derivative of each summand of the first term of d is at most
    (8/3)(A+log 3)+2 log A+2 sum_{i=0}^3 1/(13/4-i)+40 < 140.
Here (j+1)*(8/3)/(1-p)<=40, and q>=13/4. The additive constant cannot increase the logarithmic derivative. Use d(s)<=d(b)e^(140(b-s)) in the continuous cumulative formula; after including the left boundary the multiplier is at most t/(t-140). The continuous coefficient tends to d(b) by dominated convergence; d(7/8)<.006664.

The checks in power.py, ram.py and mertens_new.py use exact outward operations. For comparison with historical D01, C_(7/8)(185)<.0106*251/(251-92) and C_(7/8)(251)<.0106. By monotonicity this is strictly below D01's D(t) for every t>=185 (split at 251). At 200, 50300*C_(7/8)(200)<625=t^2/64, so the whole-ray improvement over H follows by monotonicity of C and t^2. This proves redundancy of H independently of a finite sample or baseline-choice convention. At a fixed mesh the Taylor-based recipe is also tighter than the earlier tangent-based recipe in D02_density.md: replacing the tangent exponential in its positive integral by the Taylor majorant reduces it; replacing the enlarged starting domain by the exact height reduces it further. No bound on an individual bin is inferred by subtracting two upper bounds for cumulative mass. The differences of d after telescoping are coefficients in a test-function majorant only.

An even simpler independent derivation of redundancy, without any density table, is the density-free fallback in D01_density.md. This fallback and the original strip are retained separately if a different source subset is desired.
