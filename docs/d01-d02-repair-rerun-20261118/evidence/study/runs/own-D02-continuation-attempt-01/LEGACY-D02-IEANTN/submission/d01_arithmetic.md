# Additional arithmetic consequences (checkpoint)

## Short intervals with many primes
For x≥exp(190), h=.04 x^(7/8), we prove
π(x+h)−π(x) > .0008 x^(7/8)/log(x+h).
Indeed the theta increment is ≥h−.01955[(x+h)^(7/8)+x^(7/8)]. Concavity bounds the bracket by x^(7/8)[2+(7/8) h/x]. The coefficient check is in tails.py. In particular a prime lies strictly between n^8 and (n+1)^8 for every positive integer n with n^8≥exp(190), since the eighth-power difference is ≥8n^7 and h=.04n^7. By contrast transport of the stipulated Ψ input alone as a symmetric endpoint bound yields a log² factor in the interval size; this consequence dispenses with that factor. This is not a best-known exponent claim.

## Cancellation at primorials, and a general totient/divisor bound
For a real y≥exp(400), n_y=product_{p≤y} p, L=log y, the supported symmetric conclusion is
| (n_y/φ(n_y))/(e^γ log log n_y) − 1 | < 9.2·10^−15 y^(−1/8)/L.
No sign assertion (such as the RH-related strict sign for all primorials) is made. In fact log n_y=θ(y) and n_y/φ(n_y)=Q(y) by elementary factorization. Set d=(θ(y)−y)/y. Then log θ(y)=L+log(1+d). Subtract log(1+log(1+d)/L) from the centered log-product Z in mertens.md. Its first-order part d/L cancels the endpoint term in E1. The error of this cancellation is ≤2d²/L: twice use |log(1+u)−u|≤u² for |u|≤1/2. The remaining signed integral is bounded by (1+1/L)K(L)y^(−1/8)/L and the power correction ≤1/y. Thus the upper log-error coefficient is (1+1/L)K(L)+2P²e^(−L/8)+Le^(−7L/8) with P=.01955. Exponentiation then gives the result, checked at L=400 in tails.py and monotone thereafter. A direct triangle inequality without cancellation would retain a coefficient of order .02. This is an improvement compared to applying the baseline product bound to primorials (logarithmic rather than this power of log n_y, with much larger coefficient).

For integers n≥n_Y where Y=exp(400), choose k with N_k≤n<N_(k+1) for the increasing primorials; if Y is not a prime, the largest prime p_k in N_k might be below Y. To avoid this edge, take Y0=exp(401) and the threshold n≥n_(Y0). By the interval result, the latter primorial already contains a prime >exp(400), so y=p_k≥exp(400) in every case. Factorization shows n/φ(n)≤N_k/φ(N_k) (at most k distinct primes, and p/(p−1) decreases in p). Also σ(n)/n≤n/φ(n) by the geometric series. Since p_(k+1)<1.001 p_k by the short interval theorem, log n<θ(p_(k+1))<2y, while loglog n≥loglog N_k. Therefore for both ratios n/φ(n) and σ(n)/n an upper bound is
e^γ loglog n [1+ (9.2·10^−15)·2^(1/8)·(log n)^(−1/8)/(loglog n−log 2)].
This improves the relative shape obtained by directly inserting the baseline product error; no claimed comparison with external Robin-type estimates.
