# Growing-rank transport — initial checkpoint

Assume RH. The Gaussian branch additionally uses CMSFunctionalInput.v1.population_reduction; the sparse and flat branches additionally use BRFourierInput.v1.norm_identity and BRFourierInput.v1.uniform_population_q1. For the combined minimum assume all these inputs. Write H(x)=sqrt(x) log(x), q=20582561296/24680948495, g(a)=q(1+2a), s(a)=944247/1000000+(1163388/1000000)a, f(a)=9/8+(16/15)a, and E=min(g,s,f). These are the packet's supplied population estimates, not derived from RH alone.

**Uniform theorem.** For each beta>=0 and epsilon>0, eventually in n, simultaneously for 1<=j<=floor(beta sqrt(p_n))+1,
`0 < p_(n+j)-p_n < (E((j-1)/sqrt(p_n))+epsilon) H(p_n)`.
In particular the common width at beta is E(beta)+epsilon. In the common-width statement the stronger cap min(g(beta)+epsilon,s(beta),f(beta)) is valid; at a fixed beta the two BR widths do not need epsilon.

**Count/order.** For any real y>=p_n the half-open count N=piReal(y)-piReal(p_n) is exactly the number of positive ranks k with p_(n+k)<=y: floor preserves the <= comparison to natural primes, primes are enumerated increasingly, and piReal(p_n)=n+1. Thus N>=j iff p_(n+j)<=y. For strict inequality let I_y=1 if y is a prime integer, 0 otherwise; for y>p_n, N-I_y>=j iff p_(n+j)<y. Indeed the difference removes exactly the upper-endpoint prime. In particular N>=j+1 yields the strict result even at a prime endpoint. At a fixed population anchor a with margin delta>0, after delta sqrt(p_n)>=2, N>=a sqrt(p_n)+2, which implies N>=j+1 whenever j-1<=a sqrt(p_n). One common n-threshold exists for any finite set of anchors: the prime sequence tends to infinity (strict increase gives p_n>=n+2). The lower strict inequality follows from j>=1.

**Uniform proof.** For beta>0 partition [0,beta] into finitely many equal subintervals of length h with Lh<epsilon/2, where L=max(2q,1163388/1000000,16/15). Include both endpoints. At each anchor a choose a minimizing branch for E(a); if Gaussian, use width g(a)+epsilon/2, otherwise use its exact width. Take the maximum of the finitely many thresholds in the count/order argument. For a rank take the least anchor a>=r=(j-1)/sqrt(p_n), so a-r<=h by the rank hypothesis and floor inequality. Each line increases and has slope at most L, so E(a)<=E(r)+Lh (apply the minimizing line at r); the anchor bound implies the advertised strict inequality. For beta=0 use just the zero anchor. The common-width cap follows directly from the single anchor beta and choosing the smallest of the three available widths. No explicit onset is asserted.

Status: conditional written theorem; kernel verification of the transfer is recorded below. This transfer is not a new C/AST/source-first verification. The original FFT is not supplied as PV.

## Sharper transfer using the *same* certified BR witnesses

The rounded s,f are not the smallest displayed rational leading widths available from the common flat facts. Put T=10^18. Use the following certified upper mass A, denominator D, and twice the attained maximum K:

| witness | A | D | K |
|---|---:|---:|---:|
| sparse | 887721072633027910/T | 1−119725872611533800/(2T) | 1093743426226619600/T |
| flat | 1120475208606944546/T | (15/8)(533333333333333333/T) | 1066666666666666666/T |

Write s*(r)=(A_s+K_s r)/D_s, f*(r)=(A_f+K_f r)/D_f. Equivalently their intercepts and slopes are respectively
88772107263302791/94013706369423310 and 10937434262266196/9401370636942331;
8963801668855556368/7999999999999999995 and 16/15.

**Improved theorem.** For every fixed beta>=0 and all positive eG,eS,eF, eventually in n, simultaneously for every 1<=j<=floor(beta sqrt(p_n))+1, with r=(j−1)/sqrt(p_n),
```
0 < p_(n+j)−p_n < min(g(r)+eG, s*(r)+eS, f*(r)+eF) H(p_n).
```
Each branch holds separately using only its own named inputs. Hence any subset of the branches can be used, with its respective hypotheses. A common-width bound uses the same minimum at beta; the rank-adaptive bound is at least as strong. In addition one can take the minimum with the unpadded rounded branches s(r),f(r) *uniformly in r*, since exact rational arithmetic gives s*(r)+1/2000000 <= s(r) and f*(r)+1/250 <= f(r) for r>=0. In particular taking those BR paddings gives a bound with min(g(r)+eG,s(r),f(r)), stronger than putting eG outside that minimum. The Gaussian padding remains positive. No assertion of global optimality of these three witnesses is made.

**Why the sharper data apply.** The common facts' declarations `AffineFourierPrograms.v1.challenge_sparse_witness` and `challenge_flat_witness` use the named norm identity. The witness types give the stated upper masses, positive leaks and attained positive absolute maxima for the designated windows. The node lists have length 41, terminal node 0, and m=8, by the list definitions. In `BRFourierInput.v1.denominatorFour` substitute the central value minus four times the positive leak: for sparse the central value is 1, and for flat the leak is zero. Both denominators and both maxima are positive. `BRFourierInput.v1.amplitudeMass` is exactly the witness mass (same inverse cosine amplitude), and substituting the upper mass can only lower the lower bound. Thus under RH and the named BR inputs, for each *fixed* c>0, the normalized count is eventually at least
```
(c D − A)/K − C_c [log(log x)/log x + 2 log(x)/sqrt(x)],
```
where C_c>=0 is allowed to depend on c and the witness. At c=(A+Ka)/D+e with a>=0 and e>0 the leading expression is a+eD/K. Both error summands tend to zero (log t=o(t) at t=log x, and log x=o(sqrt x)); hence half the positive surplus is a valid eventual margin. This yields GoodCoefficient on each padded sharper line. The finite-anchor proof above can be applied to each line separately and the three resulting thresholds maximized; split each padding into two halves, one for the pointwise input and one for the mesh. Equivalently use compactness: for a continuous curve l and target l(r)+e, choose a>r close enough that l(a)+e/2<l(r)+e. The sets where both strict inequalities persist are open; select a finite subcover of [0,beta]. This works with independently chosen e for each branch and requires no uniformity of C_c.

A symbolic version replaces each A by the corresponding actual mass, i.e. the integral on [0,1] of the absolute nodal cosine polynomial by the named norm identity; the same proof applies and can only improve the bound. No tighter numerical evaluation of those integrals is asserted. With the sharp leading minimum E*=min(g,s*,f*), the result can also be written with a positive o(1) padding uniform in the rank range: apply the theorem with all paddings 1/k, choose increasing thresholds N_k>=k, and take padding 1/max{k:N_k<=n} after the first threshold. This diagonal argument gives neither a numerical rate nor the eventual bound at zero padding.

## Optional n-only normalization (written)

Use the additional named prime-growth input PNT, piReal(x)~x/log x (also recalled in CMS following (1.12)). It is not needed above. At x=p_n, the count identity gives n+1~p_n/log p_n. Taking logs gives log(n+1)=log p_n−log log p_n+o(1), hence log p_n/log n→1 and p_n/(n log n)→1. For n>=2 set X=n log n and V=sqrt(n)(log n)^(3/2). Then H(p_n)/V→1. For j through floor(beta sqrt X)+1 the new r'=(j−1)/sqrt X belongs to [0,beta], and r=r' sqrt(X/p_n) differs uniformly by o(1); eventually r<=beta+1, so apply the proved theorem at beta+1 (do not simply identify the two floor bounds). Every affine branch is Lipschitz and bounded on [0,beta+1]. First use half the prescribed positive paddings in the prime-based theorem, then for all ranks absorb the uniform o(1) change of each padded branch times H/V into the remaining halves. Thus the improved theorem holds with r' and V on the n-only rank domain. This does not require an effective version of PNT and provides no explicit onset.

## Separate explicit baseline

Under the preserved RH+Green+Nicolas+BPT package only, set c0(r)=(9/8)(r+18203/20000). For 0<=r<=(16)(8/9)−18203/20000, C=max(103/100,c0(r)) is in the permitted range and the strict-open count at x=p_n>=exp(24) is greater than r sqrt(x)+(21/5)sqrt(x)/log(x). For t=log x>=24 the function exp(t/2)/t increases, and (21/5)exp(12)/24>1 even using exp(12)>=13. Thus the baseline already gives the strict rank bound with C for any rank with normalized value r in this range and x at its explicit onset. At r=1 its inverted width is 343827/160000. The new eventual bounds do not inherit that onset. This is comparison with the packet baseline only.

## Sources and scope

- `/task/COMMON_FACTS.md`, (1)–(3) and the preserved baseline. `/source_pv/EXPOSURE.json` identifies A_flat; no application modules are importable here.
- `/source_pv/FLAT_FACTS.txt`: witness theorem declarations at lines 6–10; flat nodes/width/witness at 16–116, sparse at 140–271; amplitudeMass / denominatorFour at 303–324; norm_identity, error and uniform_population_q1 at 332–435; population_reduction at 441–443; nodalPolynomial at 28412; GoodCoefficient at 28976, SourceCMSPopulation at 29007, halfOpenCount at 29076, normalizedPopulation at 29131, piReal at 29179. The corresponding exact trees in `FLAT_FACTS.json` govern, not display approximations.
- Frozen `CMS1708.04122v2.txt`, equations (1.3), (1.11)–(1.13), Theorem 3, §5; `Blanquer_Robles_2026.txt`, Theorem 1 and §3 (including exterior wings, §3.3). The named predicates are supplied formal interfaces and are not silently identified with all statements of the original papers.
- Formal representation: the local transfer file uses Mathlib natural nth/counting and floor/ceil for real endpoints. Its `Good` differs from the display only by multiplication association. `GaussianCurve`, `SparseCurve`, `FlatCurve`, `SharpSparse`, `SharpFlat` are explicit hypotheses of the transfer, not newly declared axioms. The analytic/witness substitutions are written above; this arm does not recheck the original proof bodies directly.
- Coordinator Gaussian verification is kernel-only. Coordinator rounded BR has both kernel and actual C-source/AST/execution/numerical-to-ANT routes. This submission does not recheck the C parser, port correspondence, or execution semantics; no verification of native compilation, runtime, OS or hardware is inferred. The sharper arithmetic and rank transport are not new source-first C/C++/CUDA PV. No claim for the incomplete original large FFT route.

Verification command: `cd /work/submission && /bin/lean -t 0 Transport.lean` (non-login /bin/bash). See verification.txt. The conditional endpoint, packet and sharper transport proofs passed; only standard Lean axioms appear. The optional PNT and explicit baseline arguments are written only. Earlier failures included natural-cast simplification, composition of asymptotic limits, and incorrect attempts to treat pointwise thresholds as uniform without a finite subcover.
