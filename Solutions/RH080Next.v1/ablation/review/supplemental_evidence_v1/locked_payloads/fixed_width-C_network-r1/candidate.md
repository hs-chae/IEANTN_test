# Conditional width–population transfer

Let (x>1), (y=x+csqrt xlog x), (N(c,x)=pi_{mathbb R}(y)-pi_{mathbb R}(x)), and (N^circ(c,x)=#{p	ext{ prime}:x<p<y}). Here (pi_{mathbb R}(t)=operatorname{Nat.primeCounting}(lfloor t
floor_+)). Write (mathrm{Good}(alpha,c)) for (mathrm{GoodCoefficient}(alpha,c)): (c>0) and eventually (N(c,x)/sqrt xgealpha+delta) for some (delta>0). The thresholds may depend on the parameters. All RH below is ordinary zeta RH.

## Main result from the three supplied width curves

Put (q=20582561296/24680948495) and
[
 G(a)=q(1+2a),qquad S(a)=(944247+1163388a)/10^6,qquad F(a)=9/8+(16/15)a.
]
The Gaussian route uses RH and `CMSFunctionalInput.v1.population_reduction`, and proves (mathrm{Good}(a,G(a)+epsilon)) for each (epsilon>0). Each affine route uses RH and **both** `BRFourierInput.v1.norm_identity` and `BRFourierInput.v1.uniform_population_q1`; it proves (mathrm{Good}(a,S(a))) or (mathrm{Good}(a,F(a))), respectively. None is treated as an unconditional Lean theorem about prime populations.

Define the two active switch targets and their widths:
[
 u=544470055511653/2490320656859788,quad v=542259/290164,qquad
 U=3731134672774344/3112900821074735,quad V=9048441/2901640.
]
For (age0) the lower envelope (E(a)=min{G(a),S(a),F(a)}) is
[
 E(a)=egin{cases}
 G(a) & 0le a<u,\
 S(a) & ule ale v,\
 F(a) & v<a.
 end{cases}
]
Indeed (G-S=(2q-1163388/10^6)(a-u)) and (S-F=(1163388/10^6-16/15)(a-v)), both slope differences positive, (0<u<v), and (U=G(u)=S(u)), (V=S(v)=F(v)). On the left (Gle Sle F); between switches (Sle G,F); on the right (Fle Sle G). The G–F crossing (172404138261/356130660736) lies strictly between (u,v), above the sparse branch, and is not an active switch.

Precisely, the widths certified by **direct application of these three curves and monotonicity** are
[
 (E(a),infty)  (0le a<u),qquad [E(a),infty)  (age u).
]
This is the union of (G(a)<c, S(a)le c, F(a)le c): increasing (c) eventually increases (y), hence does not decrease the count; decreasing the target retains the margin. Since all width curves have positive slopes, using a higher target cannot enlarge this union. At (u) equality is supplied by (S); at (v) either affine curve works. An infimum of recipe widths is not the actual optimum over primes. Even on the Gaussian equality width at (0<a<u), every nonnegative (b<a) is Good there by taking (epsilon=G(a)-G(b)>0) at target (b); this implies a limiting lower density at least (a), but not a uniform positive margin above (a). At (a=0) the count is nonnegative; the Gaussian route does not give prime existence at width (q).

Equivalently for a fixed width (c), there are no certified nonnegative targets if (cle q) in this recipe. For (q<c<U) the certified targets run from zero up to ((c-q)/(2q)), **excluded**; for (Ule cle V) they run through ((10^6c-944247)/1163388), **included**; for (c>V) through ((15/16)(c-9/8)), **included**. This follows by strict increase and inversion of each branch, with the attainment rule at (U).

Since (U<3<V<5), the exact maximal **direct targets of these width-line recipes** are
[
 A_3=685251/387796quad(	ext{sparse}),qquad A_5=465/128quad(	ext{flat}).
]
They give genuine (mathrm{Good}(A_i,i)), (i=3,5), without CMS or (epsilon). In particular the population lower bounds are strictly greater than (A_isqrt x) eventually, and retain a positive normalized margin. The word maximal here applies to the explicit curve substitutions, **not** to provable targets: a positive margin at (A_i) itself gives a larger target with some unspecified increment, and the witness-level refinement below gives explicit increments.

## Strict endpoints and rank

For (x>1, c>0), the half-open count exceeds the strict-open count by exactly the indicator that (y) is an integer prime. Thus (mathrm{Good}(alpha,c)) with margin (delta) implies (N^circ(c,x)ge(alpha+delta/2)sqrt x) eventually: impose also (xge(2/delta)^2). The implication is uniform over real (x) at fixed parameters. In Lean the strict count is represented by (pi'(lceil y
ceil_+)-pi_{mathbb R}(x)), where (pi'(b)) counts natural primes strictly below (b); a separate finset-membership and cardinality proof identifies it with the actual strict-open population. The bound by one also follows because (lfloor y
floor_+lelceil y
ceil_+) and one step of (pi') adds at most one.

Consequently at (p_n=operatorname{Nat.nth}operatorname{Nat.Prime}(n)), for all sufficiently large (n), every integer (1le mle(alpha+delta/2)sqrt{p_n}) satisfies (p_n<p_{n+m}<p_n+csqrt{p_n}log p_n). To check ranks, (pi'(p_n)=n) by the zero-based enumeration, and its next step adds one since (p_n) is prime, giving (pi_{mathbb R}(p_n)=n+1). A strict count of at least (m) means (pi'(lceil y
ceil_+)ge n+1+m); if (p_{n+m}gelceil y
ceil_+), monotonicity would give (pi'(lceil y
ceil_+)le n+m), contradiction. The natural-rank strict upper bound is equivalent to (p_{n+m}<y); the lower bound uses strict monotonicity of the enumeration. Finally (p_nge n+2) transports the eventual threshold to indices. This applies in particular to both fixed widths and to any input (mathrm{Good}) below.

## Exact comparison to the supplied original octic baseline

Under its **separate** RH+Green+Nicolas+BPT package, the preserved theorem is (N^circ(c,x)>(O(c)+(21/5)/log x)sqrt x) for (xgeexp(24)), (103/100le cle16), where (O(c)=8c/9-18203/20000). Only invert the leading term at targets in ([973/180000,2396173/180000]), equivalently (W(a)=(9/8)(a+18203/20000)in[103/100,16]).

| Width | Old leading (O) | Gain (A_c-O(c)) | Old leading width at (A_c) | Width saved |
|---|---:|---:|---:|---:|
| 3 | 105391/60000 | 61212941/5816940000 | 46719158823/15511840000 | 183638823/15511840000 |
| 5 | 636173/180000 | 70933/720000 | 3270933/640000 | 70933/640000 |

Both old inverse widths are in range; the savings are (9/8) times the density gains. More generally on the stated inverse domain the exact scalar gain is (W(a)-E(a)), with (E) piecewise as above. Its slopes are (9/8-2q<0, 9/8-1163388/10^6<0, 9/8-16/15>0). Its minimum occurs at (v) (in the domain), where it equals (13152201/1658080000>0). For an unattained Gaussian width, a smaller positive epsilon than the scalar gap still gives a genuine width smaller than (W(a)). Equivalently the fixed-width leading gain on ([103/100,16]) is the piecewise inverse density minus (O(c)); its minimum is at (V), namely (4384067/621780000), since the first two inverse slopes are less than (8/9) and the final inverse slope is greater. These are comparisons of leading expressions, not an inequality between finite-(x) certified right-hand sides with the old residual included. The original leading-count-1 guarantee at width (343827/160000) retains its explicit onset (xgeexp(24)). None of the new bounds inherits that onset, and no literature-wide claim is made.

## Optional refinement: keep the frozen BR witness operands instead of rounding to the lines

This uses additional statement-level data of the same supplied witnesses and the same named BR inputs, not just the three stated width curves. It does not alter their envelope. For each window let (D) be its exact denominator, (M) its attained spectral maximum, and (B) its certified upper bound for the amplitude norm. The consumer yields Good at **every** (a<(cD-B)/(2M)) for (c>0), since the true norm is at most (B) and the error tends to zero. No Good assertion at equality follows here. The operands are:
- Sparse: (D=1-4cdot119725872611533800/(8cdot10^{18})), (M=546871713113309800/10^{18}), (B=887721072633027910/10^{18}).
- Flat: (D=15cdot533333333333333333/(8cdot10^{18})), (M=533333333333333333/10^{18}), (B=1120475208606944546/10^{18}).

The better of these two operand-level limits at width 3 is the sparse (L_3=193269011844967139/109374342622661960); at 5 it is the flat (L_5=31036198331144443607/8533333333333333328). These imply eventual half-open and strict-open lower densities at least (L_i-eta) for each (eta>0) (threshold may depend on (eta)); equivalently their respective liminf bounds are at least (L_i). For example the exact Good targets (1767041/1000000) and (3637/1000) exceed (A_3,A_5). The exact limiting density gains over (O(3),O(5)) at this second tier are (1726734183826542841/164061513933992940000) and (9864964558708324124141/95999999999999999940000); these refer to limits, not positive margins at those limits. The operand bounds are not proved to be exact norms or universal optima.

## Provenance, replay and limitations

- Assigned common definitions: `/source_pv/source/IEANTN/Vocabulary/CMSFunctional.lean` lines 60–80; input aliases/interfaces in `IEANTN/Nodes/CMSFunctionalInput/v1/Conclusions.lean:9` and `IEANTN/Nodes/BRFourierInput/v1/Conclusions.lean:25–44` under that source root. Exact exported expressions in `/source_pv/FLAT_FACTS.json`.
- CMS primary: `/corpus/literature/CMS1708.04122v2.pdf`, definition (1.3), (1.12), Theorem 3 (1.13) (text companion lines 271–275), proof §5. BR primary: `/corpus/literature/Blanquer_Robles_2026.pdf`, §2.1 Lemma 5 norm identity (text line 138 onward) and §3 Proposition 6 (6), ordinary RH principal-character conductor-one specialization (text lines 336–359, 480–486). With (Q(x)={1}), use (eta(x)=log x/sqrt x). The imported interfaces preserve the general window hypotheses and the named analytic inputs; the new Lean files do not prove those analytic inputs from RH alone. Original octic baseline: `/task/COMMON_FACTS.md`, “Original comparison”; frozen coordinator locator `PrimeInterval.v4.optimized_strict_family` in `/corpus/literature/BASELINE_THEOREM_MATRIX.md`.
- Imported statement roots: `RH080EstimatePack.lean:8–21` under the assigned source root, `RH080Exposure.Estimates.gaussian/sparse/flat`, with Gaussian consumer `Scaled40ActualConsumers.lean:47`; affine providers `PopulationMatchedControl.lean:15,23` and consumers `WeightedPopulationSolution.lean:18,45`. For the optional refinement see the operands in those same affine proofs and the general padding and vanishing-remainder consumer `ExplicitBRPopulationConsumer.lean:53–93`.
- Run `/bin/lean /work/submission/Transfer.lean` and `/bin/lean /work/submission/Direct.lean` with the assigned bounded wrapper (Lean 4.34.0-rc2). The submitted successful runs report only propext, Classical.choice, Quot.sound for the printed theorem roots. The principal comparisons and both fixed-width counts (including the strict finset interpretation and generic rank transport) are kernel replayed. The full inverse description, minimum gain calculations, and the application of generic strict transport to the optional refinement are also given as written derivations; no claim that every sentence has a separate Lean declaration. `arithmetic.py` checks exact rational identities independently; it is not an analytic proof.
- This replay uses **kernel-only** numerical providers. The common packet separately reports completed C-source/AST/execution/numerical-to-ANT routes for the two affine windows. The shared C files `/source_pv/population_norm.c` and `/source_pv/flat_population_norm.c` are not themselves proofs. Here no new C execution, AST-to-source proof or source-first port was replayed. Any coordinator PV scope is the two actual integer numerical programs with their specified port/semantics, not validation of arbitrary C/C++/CUDA, compiler or runtime/OS/hardware. Gaussian verification is kernel-only; the original large FFT migration remains incomplete. Merely reading an exposure or status label establishes no theorem.
- Negative work retained: initial Lean attempts treating reducible abbreviations as syntactically identical under `unfold`/`rw` failed; `omega` alone did not prove the prime-membership conjunction; the direct consumer initially had an ambiguous `node`. Fixed by explicit unfolding, structured membership proof and the explicit window namespace. No proof at the left Gaussian equality branch, direct BR limit equality, or new explicit onset is claimed.
