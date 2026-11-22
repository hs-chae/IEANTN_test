# Actual GM primitive → J → actual prime-counting transfer

All new statements below were proved with standard-three-axiom Lean, conditional on the exact original published GM and Büthe source predicates. They are not a proof of GM itself or of the stronger .076 spectral-correlation branch.

## Exact source statement and actual quantity

Grenié–Molteni, *Explicit smoothed prime ideals theorems under GRH*, arXiv1312.4465v4, Theorem1.1, PDFp3, states for the rational field under ordinaryRH and everyx≥3:

|ψ₁(x)−x²/2| ≤.0462 x^(3/2)+1.838x+1.9851+.5097/x.

Their actual ψ₁ is ∫₀ˣψ(t)dt (definitionPDFp1) and has the finite Mangoldt representation in§1. `ActualGMPrimitive.gmPrimitive_eq_integral` proves precisely that representation, including ordinary prime-power endpoints. It uses a continuous finite max(0,x−n) representation, proved right derivativesψ−x and actual integration, rather than assuming a desired J bound.

`ActualJIdentity.actual_J_eq_riemann` proves for every positiverealx that the actual finite sum Σ[n≤floorx]Λ(n)/logn equals `IEANTN.riemannPrimeCounting x`. The proof uses exact prime-power reindexing, log(p^k)=klogp, prime cardinal counts and finite support of the actual root-counting series. NoRH or analytic/certificate premise is used.

The actual symmetric principal-value li derivative and offset were proved earlier. Combining them with the finite Abel identity gives, for1<a≤b:

T(b)−T(a)=∫ₐᵇ(ψ(t)−t)/(tlog²t)dt,

where T(x)=J(x)−li(x)−(ψ(x)−x)/logx and J is the actual vocabulary function.

## Integration by parts with every source term

Put A=.0462,B=1.838,C=1.9851,D=.5097 and
E(t)=A t√t+B t+C+D/t,
w(t)=1/(tlog²t),
k(t)=1/(t²log²t)+2/(t²log³t)=−w'(t).

The actual primitive F(t)=∫₀ᵗ(ψ−u)du is continuous and has the required right derivatives. Thus the ordinary-endpoint integral is exactly

∫ₐᵇ(ψ−t)w =F(b)w(b)−F(a)w(a)+∫ₐᵇ F(t)k(t)dt.

All jumps are included. From the literal source |F|≤E and k,w≥0:

|T(b)−T(a)| ≤E(b)w(b)+E(a)w(a)+∫ₐᵇ E(t)k(t)dt.

This full integral envelope, with C and D inside both the endpoint and integrand, is already a completed theorem in `ActualGMTransfer`. No end-target J error appears among its hypotheses.

## Closed whole-ray bound and explicit allowances

Let Φ(t)=√t/log²t and
K(t)=6AΦ(t)−B/logt−E(t)w(t).

For logt≥8, exact differentiation gives

K'(t)=E(t)k(t)+A(3/2−12/logt)/(√tlog²t)+D/(t³log²t) ≥E(t)k(t).

The constant C cancels from this derivative because it is retained in E(t)w(t); D contributes the displayed nonnegative allowance. Integrating the derivative inequality, retaining both primitive endpoints, and dropping only nonpositive terms gives

E(b)w(b)+E(a)w(a)+∫ₐᵇEk ≤6AΦ(b)+2E(a)w(a)+B/loga.

Use a=exp8. Büthe2015 Theorem2 Eq1.5 andEq1.8 give

|T(a)| ≤1.94√a/loga=1.94exp4/8.

The kernel-checked exact scalar inequality is

1.94exp4/8 +2[(.0462exp8·exp4+1.838exp8+1.9851+.5097/exp8)/(64exp8)] +1.838/8 ≤14.

This line shows exactly where C and D are paid. They were not omitted from the source or silently set tozero. Since6A=.2772, the resulting completed actual theorem is

|J(x)−li(x)−(ψ(x)−x)/logx| ≤14+.2772√x/log²x, every realx≥exp8.

The exact source predicates are ordinaryRH, the published four-termGM primitive theorem and the two original Büthe anchor statements. There is no unverified numerical zero list, new axiom, sorry, native execution axiom, derivative premise or desired J-bound premise.

## Actual prime-counting consumers and network edges

Define the actual Q(x)=J(x)−π(x). The completed generic relay is

|π(x)−li(x)−(ψ(x)−x)/logx+Q(x)| ≤14+.2772√x/log²x.

For any actualψ provider |ψ(x)−x|≤√x f(logx), this implies

−R_f(x)−Q(x) ≤π(x)−li(x) ≤R_f(x)−Q(x),

where R_f(x)=√x f(logx)/logx+14+.2772√x/log²x. The actual offset identity gives the separate absolute bound

|π(x)−Li(x)| ≤R_f(x)+|li(2)−Q(x)|.

The canonical `RHPrimeCounting.v1` node exposes the literalGM source and these derived generic/boxed/B5 outputs. Its boxed consumer uses `RHSmoothing.v1.box_psi` onx≥exp35. The matched B5 consumer has the same Q/li(2)/GM correction. Consequently the proved full-envelope gap>.546 transports as>.546√x/logx. This compares certified envelopes, not unknown actual errors. It is not called a pure scalar-coefficient PNTπ bound because actualQ remains explicit.

The sourceGM claim is literature-backed. Derived implications are completed Lean with local fresh source replay and are marked lean-noncompliant until an official Comparator workflow receipt exists. The separate610b Ramanujan branch and stronger .076 spectral transfer remain incomplete.
