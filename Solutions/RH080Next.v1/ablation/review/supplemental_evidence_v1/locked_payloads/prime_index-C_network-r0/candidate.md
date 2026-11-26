# Uniform growing-rank prime-index bounds

Let (p_n=operatorname{nth}(mathrm{Prime},n)), with (p_0=2), and put
[
s_n=sqrt{p_n},quad h_n=s_nlog p_n,quad a_{nj}=(j-1)/s_n.
]
All main bounds below use ordinary zeta RH and the named propositions
(mathrm{CMSFunctionalInput.v1.population_reduction}),
(mathrm{BRFourierInput.v1.norm_identity}), and
(mathrm{BRFourierInput.v1.uniform_population_q1}).
Each Gaussian assertion alone needs only RH and the CMS input; each BR
assertion alone needs only RH and the two BR inputs.

Write (G(a)=q(1+2a)), (q=20582561296/24680948495),
(S(a)=0.944247+1.163388a), and (F(a)=9/8+(16/15)a), with terminating decimals exact.

**Transport using only the three supplied curves.** For every fixed
(etage0,arepsilon>0), there is (n_0) such that for every (nge n_0),
simultaneously for integers (1le jlelflooreta s_n
floor+1),
[
0<p_{n+j}-p_n<h_nmin{
   min(G(a_{nj}),S(a_{nj}),F(a_{nj}))+arepsilon,   G(eta)+arepsilon, S(eta), F(eta)}.
	ag{1}
]
The fixed-(eta) cap includes the final rank and needs no BR epsilon.

**Refinement using the same already-certified BR witnesses.** For each
witness let (D) be its exact denominator, (M) its attained maximum,
and (U) its certified amplitude norm cap. Use the following exact values:
[
egin{array}{c|ccc}
 &D&M&U\ hline
s &1-4cdot119725872611533800/(8cdot10^{18})
 &546871713113309800/10^{18} &887721072633027910/10^{18}\
f &15cdot533333333333333333/(8cdot10^{18})
 &533333333333333333/10^{18} &1120475208606944546/10^{18}
end{array}
]
Define (S_*(a)=(U_s+2M_sa)/D_s), (F_*(a)=(U_f+2M_fa)/D_f).
Under the same hypotheses and quantifiers the following stronger bound holds:
[
0<p_{n+j}-p_n<h_nmin{G(a_{nj})+arepsilon, S_*(a_{nj})+min(arepsilon,1/2000000), F_*(a_{nj})+min(arepsilon,1/250)}.
	ag{2}
]
In particular the two original BR lines hold exactly and rankwise, uniformly
on the full band, even without the CMS input. The limiting refined envelope
(E=min(G,S_*,F_*)) has Gaussian, sparse, flat pieces in that order.
For (L(a)=u_L+v_La) the two switches are
((u_{S_*}-u_G)/(v_G-v_{S_*})) and
((u_{F_*}-u_{S_*})/(v_{S_*}-v_{F_*})), about (0.2186331,1.822041).
The exact rational comparisons are proved in Lean; these decimals are
illustrative. The width in (2) is at most (E(a_{nj})+arepsilon) and
at most (min(G(a_{nj})+arepsilon,S(a_{nj}),F(a_{nj}))).
All lines are increasing, so (2) implies (1), including its cap.
For (eta=0) the band consists of (j=1). These are envelopes of available
certified bounds, not assertions of sharpness for the actual primes.

## Proof

**Exact order and endpoints.** For (yge0) and (kge0),
(pi_{mathbb R}(y)) counts primes (le y) because natural floors preserve
(ple y) for (pinmathbb N). Strictly increasing enumeration gives
(p_kle y) iff (k+1lepi_{mathbb R}(y)): there are at least (k+1)
primes if (p_kle y), at most (k) otherwise. In particular
(pi_{mathbb R}(p_n)=n+1). For (yge p_n), (jge1), setting
(N_y=pi_{mathbb R}(y)-pi_{mathbb R}(p_n)) gives
[
 p_{n+j}le y Longleftrightarrow jle N_y,qquad
 p_{n+j}<y Longleftrightarrow jle N_y-mathbf1_{{y	ext{ is prime}}}.
]
Here the indicator means equality to a prime as a real number. Removing
that endpoint removes precisely one prime when present, even for (y=p_n)
where subtraction is truncated at zero. The Lean strict proof splits on
(y=p_k); in that case the rank inequality is (n+j<k). In particular
(j+1le N_y) implies (p_{n+j}<y), also by
(p_{n+j}<p_{n+j+1}le y). The hypothesis (jge1) is essential for the
strict bridge as worded. Strict growth gives (p_nge n+2), so (p_n	oinfty).

**Transfer of one point.** If (operatorname{GoodCoefficient}(b,c)),
its margin (delta>0) gives (N(c,p_n)ge(b+delta)s_n) eventually.
Take (n) also so large that (delta s_nge2); then for every (jge1)
with (j-1le b s_n), the count is (ge j+1).
Apply the strict bridge at (y=p_n+ch_n); (c,h_n>0).
At (b=eta) this applies precisely to the specified band, by the natural
floor inequality. Applying all three points at (eta) proves the cap.

**Uniform profile.** For an affine line (L(a)=A+Ba), (Bge0),
suppose for every (bge0,eta>0) that (operatorname{GoodCoefficient}(b,L(b)+eta)).
Given tolerance (e>0), use the finite upper mesh (it) with
(t=e/[2(B+1)]) and (0le ilelceileta/t
ceil).
At each point transfer its width with (eta=e/2), then take the maximum
threshold. For a given (a=a_{nj}) choose (i=lceil a/t
ceil);
(ale it<a+t), so (L(it)+e/2le L(a)+e).
For an exact pointwise width, monotonicity in the width gives the required
perturbed curve (eventually (x>1)). This proves (1).

**Refinement.** The affine BR consumer gives a good coefficient if
(a<(cD-|f|_1)/(2M)); its logarithmic remainder tends to zero at each
fixed (c). The attained maxima, denominators and norm caps in the table
satisfy its other premises, including support-five padding. For
(c=(U+2Ma)/D+eta), the right side is at least (a+eta D/(2M)>a).
Thus the mesh applies with the two tolerances in (2).
Exact rational arithmetic gives (S_*(a)+1/2000000le S(a)) on (age0)
and (F_*(a)+1/250le F(a)); the flat slopes are identical. No zero
tolerance is used at the Gaussian or refined BR infimal lines.

## Optional n-only normalization (written)

Add the single explicitly used prime-growth premise (p_n/(nlog n)	o1)
(the nth-prime form of the prime number theorem). Put (T_n=sqrt{nlog n})
and (Lambda_n=T_nlog n). For every (etage0,arepsilon>0), eventually
uniformly for (1le jlelflooreta T_n
floor+1),
[
0<p_{n+j}-p_n<Lambda_n,{E((j-1)/T_n)+arepsilon}.
]
Indeed (s_n/T_n	o1) and (log p_n/log n	o1), the latter by
(log p_n=log(nlog n)+o(1)) and (loglog n=o(log n)).
Consequently (h_n/Lambda_n	o1). If (z=(j-1)/T_nleeta), then
(a=zT_n/s_nleeta+1) eventually and
(|a-z|leeta|T_n/s_n-1|	o0) uniformly.
Apply (2) on the (eta+1) band with tolerance (arepsilon/4).
The finite minimum of affine lines is Lipschitz; its values are bounded
on ([0,eta+1]). Hence both the change in argument and the scale
multiplication introduce errors tending uniformly to zero, leaving the
claimed strict bound. Replacing the cutoff directly at identical (eta)
without this enlargement would need a one-sided prime-growth statement.

## Scope and verification

Run `/bin/lean /work/submission/Transport.lean`. The Lean statements are
`GrowingRank.common_curves`, `GrowingRank.refined_curves`,
`GrowingRank.br_exact_rounded_rankwise`, with exact bridge
`halfOpen_order` and `strict_order`. The code also checks the refined
switches, the prime-at-upper-endpoint case and the zero cutoff. No new
axioms, sorry, or unverified numerical premises are used. The optional
n-only result is not claimed Lean-checked.

CMS locator: frozen CMS1708.04122v2, Thm. 3 (1.13) with (1.3), (1.12).
BR locators: frozen Blanquer–Robles v2 §2.1 Lemma 5 (Fourier pair and norm),
§3 Proposition 6 (uniform count), specialized to (Q(x)={1}), with the
paragraph “The moduli 1 and 2” for ordinary RH. Exact typed interfaces are in
`/source_pv/source/IEANTN/Nodes/{CMSFunctionalInput,BRFourierInput}/v1/Conclusions.lean`.
These are source-backed hypotheses, not analytic theorems proved in this file.

Named estimate roots: `/source_pv/source/RH080EstimatePack.lean`.
Refinement: `PopulationMatchedControl.lean` (kernel-only witnesses),
`IEANTN/Nodes/AffineFourierPrograms/v1/Conclusions.lean` (exact witness types),
`WeightedPopulationSolution.lean` (denominator arithmetic),
`ExplicitBRPopulationConsumer.lean` (support-five padding and remainder).
Count/order sources: Mathlib `NumberTheory/PrimeCounting.lean` and
`Data/Nat/Prime/Nth.lean`. The Gaussian route's eligibility/Fourier and
numerical bounds and the BR norm certificates used here are kernel results,
not source-first PV. The separate coordinator C-source/AST/execution routes
are not replayed or used here. No claimed C/C++/CUDA, compiler, runtime, OS
or hardware correctness follows; no large FFT migration is claimed.

The preserved comparison's limiting width is
((9/8)(a+18203/20000)) only in its stated coefficient range and with
its separate assumptions. Its strict-open count can be applied at
(x=p_n) with (a=a_{nj}), (p_nge e^{24}), and this coefficient
in range: the leading count already exceeds (j-1), so it includes the
target prime. Neither that explicit onset nor one for any new bound is
obtained for (1) or (2).

## Negative checks and non-effective limits

An exact finite right-neighborhood cover from pointwise BR margins alone
was not justified. In a monotone count model, for integer scale t>4 let
the normalized count at parameter a be floor(t d_t(a))/t, where d_t(a)
equals (1+a)/2 below 1-4/t, equals 1-2/t on [1-4/t,1), and equals a+1
from 1 onward. Every fixed a>=0 eventually has a positive margin above a,
but the moving density a=1-1/t has count t-2, below rank t. This is not a
prime counterexample; it isolates the quantifier error. The exact rounded
BR rankwise proof uses certified slack instead.

Likewise an infimum is not automatically attained: in a monotone
normalized count model with limiting density max(0,(c-A)/B), A,B>0,
all positive perturbations of A+Ba have positive margin, but A itself
can have zero count. Gaussian epsilon cannot be dropped by this argument.

A diagonal choice in (2), using tolerances 1/m and bands beta=m for each
positive integer m, gives some increasing unbounded allowable cutoff and
a vanishing uniform tolerance along it. This yields no explicit rate:
choose increasing thresholds N_m>=m for these countably many statements
and use the largest m with N_m<=n. The submitted kernel theorems retain
the stated fixed-band quantifiers.
