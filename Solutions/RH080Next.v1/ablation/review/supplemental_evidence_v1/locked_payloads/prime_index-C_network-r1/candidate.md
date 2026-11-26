# Growing-rank transport (early written result)

Write H(x)=sqrt(x) log(x), p_n=Nat.nth Nat.Prime n. Assume RH and
CMSFunctionalInput.v1.population_reduction for the Gaussian curve, and RH
and both BRFourierInput.v1.norm_identity and
BRFourierInput.v1.uniform_population_q1 for the sparse and flat curves.
All three together yield, for each fixed beta>=0 and eps>0, eventual n
and simultaneously all integer 1<=j<=floor(beta sqrt(p_n))+1,
```
p_(n+j)-p_n < H(p_n) min(G(beta)+eps,S(beta),F(beta))
G(t)=(20582561296/24680948495)(1+2t)
S(t)=(944247+1163388t)/1000000
F(t)=9/8+16t/15.
```

Proof: For y>=p_n, piReal(y)>=n+j+1 iff p_(n+j)<=y.
Indeed, the strict count pi'(m) at integer m satisfies pi'(p_k)=k
by counting entries before the zero-based entry p_k, and pi'(p_k+1)=k+1
since p_k is prime. Monotonicity gives pi'(m)>=k+1 iff p_k<m, by
comparing m to p_k or p_k+1. Apply this first with m=floor(y)+1,
then with m=ceil(y) to obtain the corresponding strict-open count:
j<=pi'(ceil(y))-piReal(p_n) iff p_(n+j)<y, for j>=1.
These are natural subtractions; j>=1 makes translation by n+1 valid.
Thus N(c,p_n)>=j iff p_(n+j)<=p_n+c H(p_n). If N>=j+1 the
strict inequality follows since p_(n+j)<p_(n+j+1). With alpha=beta,
GoodCoefficient gives N>=(beta+delta)sqrt(p_n). As p_n>=n+2 by strict
increase starting at 2, delta sqrt(p_n)>1 eventually. Integer rounding
gives N>=floor(beta sqrt(p_n))+2, so the strict bridge applies to
every allowed j. Use the three eventual statements and take their common
threshold to obtain the minimum. No explicit onset is claimed. Gaussian
eps is mandatory at this stage.

The zero-epsilon envelope has its active switches at
544470055511653/2490320656859788 (G=S) and 542259/290164 (S=F).
The G=F intersection lies strictly between them and is inactive.
This is a lower envelope of supplied upper bounds, not a sharpness claim
about actual prime gaps.

The bridge and cap bounds are kernel-checked in `Transport.lean`; this is not a source-first PV result. Primary coordinator inputs: /task/COMMON_FACTS.md (1)--(3),
/source_pv/source/RH080EstimatePack.lean. Neither comparison-baseline
onset nor any other analytic premise is used here.

## Uniform profile inside the cap

Let W=(p_(n+j)-p_n)/H(p_n), t=(j-1)/sqrt(p_n), and E=min(G,S,F).
For all allowed j, the cap is exactly t<=beta, by the natural floor
inequality. For each fixed beta>=0 and eps>0, eventually, simultaneously:
```
W < min(E(t)+eps, S(beta), F(beta)).
```
For each line a+b*t, use grid points i*d, 0<=i<=floor(beta/d)+1,
with d=eps/(2(b+1)). At i=floor(t/d)+1 we have t<=i*d<=t+d.
Use the fixed-cap theorem with tolerance eps/2 there, and take the
maximum threshold over the finite grid. No uniformity of the analytic
input in alpha is assumed. The BR cap separately clips the result.
This implies a uniform asymptotic upper profile (not attainment);
at beta on/above the first switch the fixed-cap result is strictly
below E(beta) with RH+BR alone. Below the switch no zero-epsilon
Gaussian conclusion is asserted.

There is also an exact lower-order saving: for each GoodCoefficient
(beta,c), its positive margin delta satisfies, eventually for all allowed j,
p_(n+j)-p_n <= c H(p_n)-2 delta sqrt(p_n)+2.
Indeed K=N(c,p_n) satisfies K-j>=delta sqrt(p_n)-1, and p_(n+K)
lies at/below the endpoint by the exact bridge. From rank n+j>=1
onward the primes are odd (the k-th prime is >=k+2), so each of
the K-j successive distances is >=2. This is not a fixed leading-width
saving.

## Separate refinement using the supplied BR witness caps

No new analytic input. Let (D,M,A) denote denominator, attained peak,
and certified upper bound on amplitude norm, respectively. In the sparse
and flat cases use (Ds,546871713113309800/10^18,887721072633027910/10^18)
and (Df,533333333333333333/10^18,1120475208606944546/10^18),
where Ds=1-4*119725872611533800/(8*10^18) and
Df=15*533333333333333333/(8*10^18).
For c=(A+2Mt)/D+eta, eta>0, the analytic leading count exceeds t
by at least eta*D/(2*M); the vanishing remainder leaves positive
margin. Applying the same finite-grid proof gives W below the minimum
of these two refined affine profiles (evaluated at t) plus any fixed
positive tolerance. Intersect with the Gaussian profile plus tolerance
and with the exact BR cap if desired. In particular both refined BR
intercepts are at least 1/2000000 below their original intercepts,
and neither slope increases. Hence the checked witness-level theorem
gives W < min(G(t)+eps,S(t),F(t)) uniformly; it does not deduce
this exact BR component from pointwise GoodCoefficient alone.

## Optional n-only form (written; added prime-growth input)

Use PNT piReal(x)~x/log x (cited in frozen CMS1708.04122v2.txt,
line 265). From piReal(p_n)=n+1, log(n+1)=log p_n-log log p_n+o(1);
thus log p_n~log n and p_n~n log n. Put L=n log n. Then
H(p_n)/(sqrt(n)*(log n)^(3/2))→1. For j<=floor(beta sqrt L)+1,
apply the prime-normalized theorem at any fixed cap beta+rho,
rho>0, since sqrt(L/p_n)→1. Uniformly there,
(j-1)/sqrt L differs from t by o(1) on the requested ranks.
E is Lipschitz (each affine slope is bounded) and bounded there,
so for any fixed eps>0, eventually the n-normalized gap is strictly
below E((j-1)/sqrt L)+eps, by using a smaller tolerance before
conversion. No explicit onset or zero tolerance follows.

## Locators and scope

CMS frozen text Theorem 3 (1.13), with (1.3), (1.12);
BR frozen text Lemma 5 in §2.1 and Proposition 6 in §3 (q=1).
Exact propositions: assigned IEANTN/Nodes/{CMSFunctionalInput,BRFourierInput}/v1/Conclusions.lean.
Witness constants: WeightedPopulationSolution.lean,
challenge_sparse_curve and challenge_flat_curve; providers in
PopulationMatchedControl.lean. Rank machinery: Mathlib/NumberTheory/PrimeCounting.lean
(Nat.count_succ, primeCounting'_nth_eq, add_two_le_nth_prime used in the consumer).
Source-first C variants for the upstream BR numerics are coordinator
results, not replayed here. This deliverable does not verify C
AST/execution, compiler, runtime, OS or hardware; nor C++/CUDA or the
incomplete original FFT migration. No RH or analytic source predicate
is discharged, and no advantage of one exposure is inferred.
