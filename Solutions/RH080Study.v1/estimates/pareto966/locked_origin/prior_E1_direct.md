# Direct pointwise transfer and an octic-only comparison

Write a=n³, b=(n+1)³, t=log n, q=1/n, s=log(1+q), D=1+q+q²/3; normalize counts by n²/t. Use increasing inclusive theta from the packet.

## Exact pointwise envelopes (both endpoints open)

For n>1, the sum of log p over a<p<b is theta(b^-)-theta(a): this is an ordinary one-sided limit, since primes in any bounded interval form a finite set. Take the applicable lower estimate for theta(v) with a<v<b and v tending to b. It becomes non-strict upon passage to the limit. Use the strict upper estimate at a. Thus the final count is still strictly larger than each applicable quotient below (each log p is at most log b). No endpoint subtraction, no assumption that a cube of a real number is composite, and no loss of a prime if b happens to be prime.

* S = Schoenfeld (6.1), with a≥2300000000:
  `P_S = [D - (G(t)+(1+q)^(3/2)G(t+s))/(3 sqrt(n))]/(1+s/t)`,
  where G(v)=(9v²-6v)/(8π).
* B = Büthe (1.6) at b^- and (1.7) at a, with a≥1423, b≤10^19:
  `P_B = [D - (1.95(1+q)^(3/2)-0.05)/(3 sqrt(n))]/(1+s/t)`.

S and B denote the explicit source predicates, not additional conclusions assumed at cube scale. B is unconditional as published; S uses ordinary RH and its published source implication. The term -0.05 is essential in the optimized B result; reversing the error in (1.7) or applying that inequality at b as a lower bound would be wrong.

An optional pointwise improvement comes from exact partial summation. Put R(v)=theta(v)-v. The open count equals
`integral_a^b dv/log v + R(b^-)/log b - R(a)/log a + integral_a^b R(v)dv/(v log²v)`.
If R(v)≥-L(v), R(a)<U(a), substitute these estimates. The resulting bound differs from the basic unnormalized bound (b-a-L(b)-U(a))/log b by
`integral_a^b [v-a-L(v)-U(a)]dv/(v log²v)`.
One can always take the maximum of the two; neither integral nor its numerical sampling is needed for the uniform constants below. This refinement retains the correct left limit.

## Whole-domain scalar reductions

**S.** If t≥t0≥8, q≤q0≤1/1000, put
`X(t;q0) = [1+(1+q0)^2] (9(t+q0)^2-6(t+q0)) exp(-t/2)/(24π)`.
We used log(1+q)≤q and (1+q)^(3/2)≤(1+q0)^2. The t-dependent factor decreases: with v=t+q0≥8 its derivative after division by exp(-t/2) is -4.5v²+21v-6<0. Hence
`P_S ≥ 1-X(t0;q0) + (1-1/t0) q/(1+q0/t0)`.
Indeed write P_S as 1 plus the positive D-1-s/t and minus the nonnegative error, all over 1+s/t. Directly S alone gives .7437 on the exp(8) ray: use the certificate's small initial slice t∈[8,8.01] with a positive q lower bound (or use .74336 without a slice). Later, e.g. .98 from exp(16), .99 from exp(18), .995 from exp(20), .999 from exp(24), and .9999 from exp(30) follow from the same scalar bound. These are uniform written deductions, not samples.

**B.** If n≥n0≥12 and t≥t0≥2, set r=1/sqrt(n), d=1/t0, c=1-d and
`H(r)=[c r²+r⁴/3 - (1.95(1+3r²/2+3r⁴/8)-0.05)r/3]/(1+d r²)`.
Taylor's formula with nonpositive third derivative gives the upper quadratic for (1+q)^(3/2); the numerator D minus its error is positive here (for r≤.3 the error is <.22). Enlarging the denominator gives P_B≥1+H(r). On 0≤r≤.3 the numerator J satisfies J'≤.6+4(.3)^3/3-1.9/3<.003 by a very coarse bound; retaining the cubic term of the error gives the stronger J'≤2r-1.9/3-(2.925-4r/3)r² ≤2r-1.9/3. For the quotient N=J'(1+d r²)-2drJ, use J≥-r[1.95(1+1.5(.3)^2+.375(.3)^4)-.05]/3>-.73r, and d≤.5. Thus N≤2r-1.9/3+.73r²; this is negative for r≤.28, which suffices for n≥13. For n0=12 (r≤.29), retain also -2.5r² in J': indeed 2.925-4r/3≥2.5 there. Then N≤2r-1.9/3-(2.5-.73)r²<0. In all cases n≥12 use this last argument. Accordingly evaluate at an upper bound for 1/sqrt(n0). The certificate gives the finite-domain coefficients .85 from n≥12, .94 from n≥100, .98608 from n≥1950, and .9886881 from n≥exp(8).

**Simple hybrid.** Use B for exp(8)≤n≤2154433 and S afterwards: (2154433+1)^3<10^19. The numerical verifier checks .9669924 for all n≥2154433 using S: split at 2154533; on the short initial slab retain the term with q≥1/2154533, and on the rest discard that term. This replacement of the original analytic assumption package drops Green/Nicolas/BPT and adds S and B (and RH for S). Not RH-only inside Mathlib. Direct S cannot prove .8 at exp(8) by the displayed endpoint quotient; B cannot be used beyond its finite domain.

## Same inherited analytic package, simple adaptive octic cells

Let c=0.91015 and C0=(b-a)/(sqrt(a) log a)=D sqrt(n)/t. On the exp(8) ray C0>6.8>1.03, since exp(t/2)/t increases for t≥8. If C0≤16 a single application gives the coefficient
`(8/9)D-(ct-1.4)exp(-t/2)`.
Its lower bound (8/9)(1+exp(-t))-(ct-1.4)exp(-t/2) increases for t≥8: after factoring exp(-t/2) the derivative is ct/2-0.7-c-(8/9)exp(-t/2)>0. It exceeds .78146 at 8.

Otherwise k=ceil(C0/16) and take k equal-length open cells of length H=(b-a)/k, with left ends x_i. Each C_i=H/(sqrt(x_i)log x_i)≤16, and C_i≥C0/(kw) where w=(1+q)^(3/2)(1+s/t)<1.001. Since k<C0/16+1<C0/8, C_i>8/w>1.03. Cells are disjoint and strict count lower bounds add without double counting. Write their main terms as (8/9)H/log x_i, and bound their costs by (c-1.4/(t+s))sqrt(b) per cell. The resulting normalized coefficient is at least
`(8/9)D/(1+s/t) - (c-1.4/(t+s))(1+q)^(3/2) k t /sqrt(n)`.
Here D/(1+s/t)≥1. If t≤12, k t/sqrt(n)<D/8 and c-1.4/(t+s)<.794; D and (1+q)^(3/2) are each <1.001. This branch therefore exceeds .789. If t≥12 use k t/sqrt(n)<D/16+12 exp(-6)<1.001/16+.03; cost coefficient <c and (1+q)^(3/2)<1.001. This branch exceeds .804. Thus .78146 holds at exactly the inherited onset with unchanged RH+Green+Nicolas+BPT package. No optimization theorem about all possible octic consumers is asserted. This tiling's displayed guaranteed coefficient tends to 8/9-c/16=.8320045138... (maximum admissible width); it cannot compete late with a pointwise estimate tending to one. Near the onset a tiling using uniform worst-case cell geometry, instead of taking the exact single interval, loses enough to miss .78146.
