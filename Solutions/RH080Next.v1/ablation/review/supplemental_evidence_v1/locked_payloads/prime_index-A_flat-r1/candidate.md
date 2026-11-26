# Growing-rank transport

Put (s_n=\sqrt{p_n}), (H_n=s_n\log p_n), (r_{nj}=(j-1)/s_n), and let
(g(t)=q(1+2t)), (b(t)=944247/10^6+(1163388/10^6)t),
(f(t)=9/8+(16/15)t), (M(t)=\min(g(t),b(t),f(t))).
Use ordinary RH and the three named inputs in /task/COMMON_FACTS.md.
For each fixed beta >= 0 and eta > 0, eventually simultaneously for
(1\le j\le\lfloor\beta s_n\rfloor+1),
[
0 < (p_{n+j}-p_n)/H_n <
\min\{M(r_{nj})+\eta, g(\beta)+\eta,b(\beta),f(\beta)\}.
]

Exact bridge: for (y\ge p_n), the primes in ((p_n,y]) have indices
(n+1,\ldots,\pi_{\mathbb R}(y)-1), since for each integer prime
(p\le y) iff (p\le\lfloor y\rfloor). Consequently for (j\ge1),
(j\le N(c,p_n)) iff (p_{n+j}\le y) when (y=p_n+cH_n).
In particular (N(c,p_n)\ge j+1) implies (p_{n+j}<y), by strict prime
ordering; merely having (N(c,p_n)\ge j) does not. Exactly, the strict-open
count is (N-\mathbf 1_{\{y\text{ is a prime}\}}) when (y>p_n).

From GoodCoefficient(a,c), take its delta>0 and threshold. The distinct
integer primes satisfy (p_n\ge n+2), so eventually (p_n) exceeds the
threshold and (\delta s_n\ge 2). If (j-1\le as_n), the count is at
least ((a+\delta)s_n\ge j+1). Thus the transport is strict with one
eventual threshold for the entire band at a fixed anchor a.

For the rank-sensitive bound take a finite right-end mesh of [0,beta] of
step at most eta/(2L), where L=max of the three slopes, including 0 and beta.
At each mesh point a choose a minimizing line; use Gaussian with eta/2
if selected, or the exact BR coefficient. A finite conjunction of the
anchor bounds works for every rank. For the first mesh point a >= r,
(M(a)\le M(r)+L(a-r)), by evaluating a line minimizing at r.
The coefficient used at a is at most (M(r)+\eta).
Add the three independent anchor bounds at beta for the clipping term.
No moving alpha is substituted into a pointwise eventual theorem.



## Constants, hypotheses, and exactness

The three named inputs are `CMSFunctionalInput.v1.population_reduction`,
`BRFourierInput.v1.norm_identity`, and
`BRFourierInput.v1.uniform_population_q1`. Gaussian conclusions alone use
RH + the first; both BR branches alone use RH + the latter two. Use the
union of these hypotheses for the combined result. The widths apply to
strict-open intervals; there is no explicit onset. The endpoints of the
active pieces of M are
[
r_{GB}=544470055511653/2490320656859788,qquad
r_{BF}=542259/290164.
]
Specifically the minimizing line is g, then b, then f, with ties at the
junctions. The g/f crossing lies strictly between these junctions. These
comparisons are exact (see `arithmetic.py`). This is the lower envelope
of the three supplied leading lines, not an optimality assertion about primes.

At fixed beta the endpoint bound alone is
(min{g(eta)+eta,b(eta),f(eta)}H_n).
For beta at or above the first crossing one can drop the Gaussian branch
at that endpoint and get the exact BR coefficient, including at the tie.
For fixed j one can use the beta=0 Gaussian coefficient with eta for j=1;
for j>1 use arbitrarily small fixed positive beta and split the width
allowance, since s_n tends to infinity. At beta>0, even j of size
(eta s_n+O(1)) fits the anchor proof: the fixed delta absorbs any
fixed rounding error. In fact the same anchor works for
(jlelfloor(a+delta/2)s_n
floor+1) eventually.
Any finite set of exact BR anchors a can be added to the clipping rule
at ranks r <= a, without an additional width loss. The proof is the finite
conjunction of the corresponding anchor transports.

One may diagonalize the uniform additive error to obtain an unspecified
error tending to zero on each fixed band, or use a single error on bands
([0,B_n]) with some (B_n	oinfty): take increasing integer thresholds
for beta=k, eta=1/k (and require the kth threshold >= k), use the largest
k whose threshold has passed. This provides neither an effective rate nor
an unslacked eventual leading bound. In particular the Gaussian
epsilon cannot be set to zero. Replacing all fixed-a thresholds by a
threshold uniform over all real a is not justified by the curve statements.
In the proof `Transport.lean` uses three separate ceiling meshes; this is
equivalent to the single finite-mesh argument above.

## Supplement: sharper BR bounds from additional shared witness facts

The preceding result uses **only the three curves**. The following
strengthening uses the extra BR margin consumers and certified norms
in the identical flat statement corpus. It changes neither the analytic
predicates nor the Gaussian coefficient. For the sparse and flat
witnesses, respectively, use the triples (D,B,U) below, with T=10^18:
[
egin{array}{c|ccc}
& D&B&U\
s&1-4(119725872611533800/(8T))&887721072633027910/T&546871713113309800/T\
f&15(533333333333333333)/(8T)&1120475208606944546/T&533333333333333333/T .
end{array}
]
For each triple put (L_{D,B,U}(r)= B/D+(2U/D)r).
For fixed beta>=0 and any three positive losses (e_g,e_s,e_f), eventually
on the same band the normalized positive gap is strictly less than
[
min{g(r)+e_g, L_s(r)+min(e_s,1/2000000),                  L_f(r)+min(e_f,1/250)}.
]
In particular the **un-inflated nominal BR lines at the moving rank**
are both valid simultaneous upper bounds by this additional route.
Do not mistake this for an exchange of quantifiers using just (2)–(3).

Proof: for each triple the shared margin consumer supplies
GoodCoefficient(a,c) whenever (c>0) and (a<(cD-B)/(2U)), under
RH + the two BR predicates, after supplying its shared periodic norm cap.
At any mesh anchor a>=0 use (c=L(a)+e/2). All D,B,U are positive, and
((cD-B)/(2U)=a+eD/(4U)>a). On a finite right-end mesh with slope times
mesh step <= e/2, this gives the uniform rank coefficient (L(r)+e).
Use the smaller of the two positive BR losses in the displayed formula.
Exactly, (L_s(0)+1/2000000<b(0)) and (L_s'le b');
(L_f(0)+1/250<f(0)) and (L_f'=f'). Lean checks the arithmetic.
These refined bounds are not claimed optimal even for the witnesses;
the caps are upper bounds, not necessarily exact norm values.

Locators in `/source_pv/FLAT_FACTS.txt` (exact trees in the JSON):
- Consumer roots/types: 58793–58803; Gaussian curve at 3351226,
  flat curve at 3357139, sparse curve at 3357251. Counts at 28976
  (GoodCoefficient), 29076 (halfOpenCount), 29179 (piReal).
- BR predicates: 332, 383. Equality bridges to the witness consumer
  predicates: 127016 and 127024. CMS population predicate: 441.
- Sparse certificate `RH080Next.PopulationPV.kernel_only_periodic_norm`
  at 186612, consumer `RH080Next.PopulationWitness.actual_goodCoefficient_of_margin`
  at 191453; leakage, maximum and cap at 191568, 191606 and 191638.
- Flat certificate `RH080Next.FlatPopulationPV.kernel_only_periodic_norm`
  at 121794, consumer `RH080Next.FlatPopulationWitness.actual_goodCoefficient_of_margin`
  at 126598; maximum, cap and normalization at 126775, 126807 and 126833.
  The periodic bound in each case is precisely the stated cap, by unfolding
  the displayed rational definition.
- Primary paper locators: `/corpus/literature/CMS1708.04122v2.txt`,
  Theorem 3 at line 267, equation (1.13), proof §5.2;
  `/corpus/literature/Blanquer_Robles_2026.txt`, Lemma 5 at line 136
  (norm identity), Proposition 6 at line 332 and its proof through
  line 474 (population estimate and remainder). Use the exact assigned
  predicates, not the full strengths of unrelated GRH assertions.

## Optional n-only scale (written, additional hypothesis)

Assume separately (p_n/(nlog n)	o1); this is the prime-growth premise,
not a consequence asserted from the short-interval inputs. Write
(A_n=nlog n) for (nge2) and (u_n=p_n/A_n). Then
(s_n/sqrt{A_n}	o1), and
(log p_n=log n+loglog n+log u_n) gives
(H_n/(sqrt n(log n)^{3/2})	o1).
For (1le jlelflooretasqrt{A_n}
floor+1), write
(t=(j-1)/sqrt{A_n}). The prime-scale rank is (t/sqrt{u_n}),
which is at most (eta+1) eventually and differs from t by at
most (eta|1/sqrt{u_n}-1|=o(1)) uniformly. The envelope M is
Lipschitz (maximum slope suffices), and bounded on that enlarged band.
Apply the prime-scale result with beta+1, loss eta/3, and multiply
by the scale ratio. The uniform change in normalized coefficient is
(o(1)). Thus for each eta>0 the n-only normalized gap is eventually
strictly less than (M(t)+eta) over the indicated n-only band. The
same argument works with the refined leading envelope and positive losses.
It does not preserve an exact unslacked BR width under the change of scale.

## Verification and boundaries

Run `/bin/lean /work/submission/Transport.lean` (Lean 4.34.0-rc2)
and `/usr/bin/python3.10 /work/submission/arithmetic.py`. The Lean file
kernel-checks the complete count/ceil/floor/order bridge, rank
transport, nominal specialization from explicit curve hypotheses, and
refined specialization from explicit margin hypotheses. Its
`#print axioms` reports only propext, Classical.choice and Quot.sound.
It does not re-prove or import the application curve theorems in A_flat;
the upstream application to the assigned package is the written
instantiation, not a newly compiled end-to-end application theorem.
Definitions are transcribed from the shared types; the additional
`piStrict` counts integers p with (p<lceil z
ceil), equivalent
to (p<z). The original explicit-onset RH+Green+Nicolas+BPT result is
separate; no transfer of onset, constants outside its parameter range,
or universal record claim is made.

No C execution, C AST proof, or compiler validation is claimed here.
The common packet supplies completed source-first numerical-to-ANT
routes for the BR branches (not for Gaussian). The source bytes in this
arm are `/source_pv/population_norm.c` and
`/source_pv/flat_population_norm.c`; the study's source-first status
does not imply a proof of arbitrary C/C++/CUDA semantics or the host
compiler, runtime, OS, or hardware. Transport is independent of the
choice of the BR numerical route. The large FFT migration remains
outside the verified scope.

Negative work: trying a direct cast across opaque P initially failed;
unfolding to the natural cast repaired the Lean proof. A direct rewrite
of the mesh index failed while Lean exposed the ceiling, and was replaced
by changing the goal to the local index before rewriting. A final
refined-branch `convert` generated a typeclass-field equality;
explicit calculation repaired it. Discarded shortcuts were taking
the moving-rank input in a pointwise eventual assertion, dropping the
Gaussian epsilon, and counting a right-endpoint prime in a strict-open
interval without subtracting it or producing an extra prime. No
open problem is claimed solved by a numerical output or status flag.
