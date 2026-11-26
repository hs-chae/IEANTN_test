# Growing ranks at prime anchors

Let p_n=Nat.nth Nat.Prime n, s_n=sqrt(p_n), H_n=s_n log(p_n).
Write G(t)=q(1+2t), q=20582561296/24680948495,
S(t)=944247/1000000+(1163388/1000000)t, and F(t)=9/8+(16/15)t.

**Fixed cap.** For every beta>=0 and epsilon>0, eventually in n,
simultaneously for the integers 1<=j<=floor(beta*s_n)+1,
`0 < p_(n+j)-p_n < min(G(beta)+epsilon,S(beta),F(beta))*H_n`.
The Gaussian uses RH and CMSFunctionalInput.v1.population_reduction;
S and F each use RH and both BRFourierInput.v1.norm_identity and
BRFourierInput.v1.uniform_population_q1. Each branch holds separately
with its own hypotheses. No explicit onset.

**Exact bridge.** At endpoint y>=p_n put m=piReal(y) and k=m-(n+1);
here m>=n+1, so subtraction is exact. For j>=1,
p_(n+j)<=y iff n+j<m iff j<=k, by the zero-indexed enumeration:
piReal(y) counts precisely the primes among the naturals <=floor(y).
Moreover p_n<p_(n+j). The exact strict version is j<=k-e(y),
where e(y)=1 if y is itself a prime integer, 0 otherwise. Indeed if y
is a prime it is the last of the m primes, of index m-1, and otherwise
<=y and <y agree for every prime. In particular j<k always suffices
for p_(n+j)<y (the prime p_(n+j+1) is then <=y).

For GoodCoefficient(beta,c), choose its positive margin delta and
eventual x threshold. The increasing integral sequence p_n tends to
infinity (p_n>=n); hence eventually the hypothesis holds at x=p_n
and delta*s_n>1. Then k>beta*s_n+1>=j, proving the strict bound at c
by the bridge. Intersect the three tails to take the minimum. In
particular the +1 rank and the strict upper endpoint are both justified
without rounding the leading population lower bound the wrong way.

**Rank-adaptive.** Put t_(n,j)=(j-1)/s_n. For each beta>=0 and eta>0
there is a single eventual threshold for all the same ranks, giving
`(p_(n+j)-p_n)/H_n < min(G(t_(n,j)),S(t_(n,j)),F(t_(n,j)))+eta`.
Use a finite grid covering [0,beta] from above: choose a mesh h>0
so that the largest slope times h is <eta/2. At the upper node a for
each t, j<=floor(a*s_n)+1. Apply the fixed-cap result on all grid
nodes with Gaussian epsilon=eta/2 and take the maximum of their
finitely many thresholds. Each line's increase from t to a is <eta/2,
including for beta=0 (take just node 0). This uses no uniform
analytic population onset in alpha. Together with the fixed cap one
may take the minimum of the two right hand sides.

These are mathematical derivations; formal verification and more detailed
source tracking are separate. No exact Gaussian infimum attainment,
and no global optimality claim.
