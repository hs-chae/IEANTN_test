#!/usr/bin/env python3
from pathlib import Path
import json,shutil,hashlib,base64,html,re,sys
B=Path(__file__).resolve().parent
FROZEN=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-propagation-20261120/evaluator-private/final-locks/IEANTN_RH/files')
if sys.argv[1:]not in [[],['--portable']]:raise SystemExit('usage: make_review.py [--portable]')
R=B/'frozen'if sys.argv[1:]==['--portable']else FROZEN if FROZEN.exists()else B/'frozen'
N=R.parents[3]/'network'
SUP=Path('/data/ivy-rh-propagation-20261120/post-lock-verification/MertensPositive-v1/render-support')
if not (B/'render-support').exists():shutil.copytree(SUP,B/'render-support',ignore=shutil.ignore_patterns('__pycache__'))
sys.path.insert(0,str(B/'render-support'))
from latex2mathml.converter import convert
(B/'frozen').mkdir(exist_ok=True)
names=['PNT.md','Weighted.md','Intervals.md','PNTClosed.lean','PNTReduced.lean','PNTFormal.lean','PNTScalar.lean','LooseLowSum.lean','ThetaSigned.lean','WeightedConsumer.lean','Intervals.lean','InputsNotClosed.md','Ramanujan.md','RESEARCH_REPORT.md','generate_loose.py']
for n in names:
 if (R/n).resolve()!=(B/'frozen'/n).resolve():shutil.copy2(R/n,B/'frozen'/n)
nodes=['CH2/v1','ZeroCount/v1','ZetaLogDerivValues/v1','ZetaHadamard/v1','CotangentSeries/v1','Buthe/v1','Buthe2016/v1']
(B/'node-statements').mkdir(exist_ok=True)
for n in nodes:
 p=N/'IEANTN/Nodes'/n/'Conclusions.lean'
 if p.exists():shutil.copy2(p,B/'node-statements'/(n.replace('/','-')+'.lean'))
def loc(name,needle):
 s=(R/name).read_text().splitlines()
 for i,l in enumerate(s,1):
  if needle in l:
   fragment=l.strip();j=i
   while fragment.count('\\(')>fragment.count('\\)')and j<len(s):
    fragment+=' '+s[j].strip();j+=1
   return {'file':name,'line':i,'fragment':fragment}
 raise RuntimeError((name,needle))
cards=[]
def add(id,title,status,actual,source,formula,analysis,impact,files,primary):
 cards.append(dict(id=id,title=title,status=status,actual=actual,primary_claim=source,
   formulas=formula,analysis=analysis,impact=impact,
   written_source_locations=[loc(*x)for x in files],primary_locators=[{'source':s,'pdf_page':p,'locator':t}for s,p,t in primary],
   blueprint='No new standalone Blueprint label is supplied in the frozen87-file submission. The exact new-claim correspondence is its linked family manuscript and any listed Lean theorem; an inherited node contract is linked separately where applicable.'))

add('P01','Adaptive PNT ray: the central bound survives','accepted',
 'PNT.md states the coefficient A on the ray x≥exp(34); PNTFormal.actual_psi consumes the actual CH2 source contract. PNTScalar.scalar_simplify proves the final scalar simplification.',
 'Chirre–Helfgott Corollary 1.2 requires finite-height RH, T≥10⁷ and x>max(T,10⁹). Its center is x(π/T)coth(π/T), rather than x. The source statement itself is:',
 [r'\left|\psi(x)-x\frac\pi T\coth\frac\pi T\right|\le\frac{\pi x}{T-1}+\left(\frac{\log^2(T/(2\pi))}{2\pi}-\frac{\log(T/(2\pi))}{6\pi}\right)\sqrt x.',
 r'L=\log x,\quad T=20\sqrt x/L,\quad u=L/2-\log L+\log(10/\pi),\quad A(L)=.158L+(u^2-u/3)/(2\pi).',
 r'1\le(\pi/T)\coth(\pi/T)\le1+(\pi/T)^2,\quad |\psi(x)-x|\le A(L)\sqrt x\quad(L\ge34).'],
 'The chosen T increases for L≥34, exceeds 10⁷ at 34, and is less than x. Thus its source hypotheses hold on the entire ray. The centering correction in √x units is at most [π(1+1/(10⁷−1))+π²/10⁷]L/20<.158L. The frozen Lean height proof is analytic, rather than a finite sample. No zero-list evaluation is silently supplied by RH.',
 'Accepted as a written theorem from the cited inputs and as a conditional Lean composition. The original A route retains 13 named source predicates; the reduced formal route is described separately below.',
 [('PNT.md','## The new ray'),('PNTFormal.lean','theorem actual_psi'),('PNTScalar.lean','theorem scalar_simplify')], [('ch2',3,'Corollary 1.2')])

add('E01','Correction 1: Lee–Nosal 1.1 was transcribed incorrectly','comparison-error',
 'The baseline table in PNT.md attributes the first formula below to Lee–Nosal Theorem 1.1. This is prose comparison data; no frozen Lean declaration defines or consumes that transcription.',
 'Lee–Nosal v4 Theorem 1.1, PDF page 2, gives the second formula below under RH for x≥11. The missing grouping changes both logarithmic terms and the scaling of the last constant.',
 [r'F_{\rm frozen}(L)=\frac{L^2}{8\pi}-\frac L{2\pi}+1.465\log L+1.2325\qquad\text{(incorrect attribution)},',
 r'|\psi(x)-x|\le\sqrt x\,L\left(\frac L{8\pi}-\left(\frac1{2\pi}+\frac{1.465}L\right)\log L+1.2325\right)\quad(x\ge11),',
 r'F_1(L)=\frac{L^2}{8\pi}-\left(\frac L{2\pi}+1.465\right)\log L+1.2325L.',
 r'L=34:\qquad F_{\rm frozen}\approx46.983,\qquad F_1\approx63.653.'],
 'The exact trigger is the baseline row and its ensuing comparison, not an out-of-domain value. Expanding the paper’s outer factor L shows the error immediately. Exact rational-series checks independently evaluate both coefficients; approximate figures here are only for orientation.',
 'Correct the baseline formula and every comparison that uses it. This is not a counterexample to the adaptive A theorem, whose proof is based on CH2 and does not use the misquoted row.',
 [('PNT.md','1.465')], [('lee-nosal',2,'Theorem 1.1')])

add('E02','Correction 2: the two Lee–Nosal envelopes exchange order','comparison-error',
 'PNT.md says “LN 1.2 is smaller than 1.1 for L≥e⁴.” The global order is false. The comparison paragraph is written mathematics; no Lean theorem asserts this order.',
 'Lee–Nosal v4 page 2 states that Theorem 1.2 is stronger up to x≈exp(30369.581…). Its exact Theorem 1.2 coefficients are displayed below, along with the corrected difference.',
 [r'|\psi(x)-x|\le\frac{\sqrt x\,L(L-\log L)}{8\pi}\quad(x\ge101),\qquad |\vartheta(x)-x|\le\frac{\sqrt x\,L(L-\log L)}{8\pi}\quad(x\ge2657).',
 r'F_2(L)=\frac{L(L-\log L)}{8\pi},\qquad \frac{F_1(L)-F_2(L)}L=1.2325-\frac3{8\pi}\log L-\frac{1.465\log L}L.',
 r'30369.581<L_*<30369.582,\qquad F_2<F_1\ (34\le L<L_*),\qquad F_1<F_2\ (L>L_*).',
 r'F_1(10^6)-F_2(10^6)<-400000.'],
 'The derivative of the displayed normalized difference is −3/(8πL)+1.465(log L−1)/L²<0 for L≥34: (log L−1)/L decreases there, and its value at 34 suffices. This proves a unique crossing, and exact interval arithmetic brackets it as shown. L=10⁶ is a concrete counterexample to the frozen order claim.',
 'The inferred ordering cannot justify a comparison with both baselines. The direct corrected comparisons in the next card do justify the intended adaptive improvement, including for arbitrarily large L.',
 [('PNT.md','LN 1.2 is smaller')], [('lee-nosal',2,'paragraph before Theorem 1.1; Theorem 1.2, (2)–(3)')])

add('P02','Corrected comparisons: A and both additive variants beat both ψ baselines','accepted-derived',
 'The actual endpoint coefficients are A, the compiled A+.821, and the written A+.332. This card supplies a correct comparison without assuming an incorrect global order between the two Lee–Nosal theorems.',
 'Use the literal Lee–Nosal F₁ and F₂ from the preceding two cards, on their source domains. Both domains contain the entire adaptive ray. Lee–Nosal 1.2 supplies a θ bound, but no π bound of that improved shape.',
 [r'k=\log(10/\pi),\quad v=\log L-k,\quad c=1.2325-.158-\frac{k}{2\pi}+\frac1{12\pi},',
 r'\frac{F_1(L)-A(L)}L=c-\frac{1.465\log L}L-\frac{v^2+v/3}{2\pi L}>.73\qquad(L\ge34).',
 r'8\pi(F_2-A)=L(3\log L-4k+2/3-8\pi\cdot.158)-4v^2-4v/3>1.8L.',
 r'F_2(L)-A(L)>\frac{1.8L}{8\pi}>2.4\qquad(L\ge34).',
 r'.821+1.10+.278/L+14Le^{-L/2}<2.4.'],
 'For the first inequality use 1.15<k<1.16 and 3.52<log34<3.53. Each of log L/L, v/L and v²/L decreases for L≥34 because v>2. Substituting these endpoint bounds and 3.14<π<22/7 gives a lower bound exceeding .73. For F₂, the leading bracket exceeds 2.61, while [4v²+(4/3)v]/L<.77; the derivative signs are the same. These are whole-ray estimates, not extrapolated finite grids. All displayed finite numerical inequalities are checked independently by rational series.',
 'The ψ improvements against both correctly quoted Lee–Nosal theorems survive. The θ improvement against Lee–Nosal 1.2 also survives the 1.01 relay cost. The resulting π envelope improves Schoenfeld on this ray; it must not be attributed to a nonexistent π clause of Lee–Nosal 1.2. The Li₂ center adds |li(2)| explicitly as frozen PNT.md already states.',
 [('PNT.md','For comparison with Lee'),('PNT.md','At the level of published inputs')], [('lee-nosal',2,'Theorems 1.1–1.2'),('schoenfeld',3,'Corollary 1, (6.18), printed p.339')])

add('P03','Reduced PNT chain: eight precise external predicates remain','accepted-conditional',
 'PNTClosed.sharpened directly invokes PNTReduced.no_ordinate_sum and the existing Proposition 2.4, Gamma-strip and functional-equation proofs. Its only non-domain parameters are RH and the eight names shown below.',
 'The principal analytic source is CH2 Corollary 1.2, section 7’s low-zero contribution and Lemma B.1’s closed zero counts. The inherited literal contracts are preserved in the linked node statements. This review does not claim a new formal proof of those external contracts.',
 [r'|\psi(e^L)-e^L|\le(A(L)+.821)\sqrt{e^L}\qquad(L\ge34).',
 r'2\sum_{0<\gamma\le20000}\gamma^{-1}\le11.1404,\qquad11.1404-10.3194=.821.'],
 'The eight predicates are ZetaLogDerivValues.v1.logDeriv_laurent_alternating, logDeriv_neg_one, logDeriv_two, logDeriv_three_halves; CotangentSeries.v1.cot_series_zeta_values; ZeroCount.v1.rvm_error_bound, rvm_error_small; and ZetaHadamard.v1.logDeriv_partial_fractions. LooseLowSum proves the cap on the actual finite multiplicity-weighted set, including N(2π)=0 by integrality. The generated replacements retain the +.821/√x scaling through contour and limit steps. The original low-sum numerical result is replaced, rather than recovered from RH. The surviving source predicates include numerical-value and coefficient-sign information; “no separate reciprocal-ordinate sum” does not mean “all published computation eliminated.”',
 'Accepted conditional interface. The log reports the standard three Lean axioms, but no new independent full-chain compiler replay is claimed by this mathematics review. A standalone RH-only Lean theorem is not supplied.',
 [('PNTClosed.lean','theorem sharpened'),('PNTReduced.lean','theorem no_ordinate_sum'),('LooseLowSum.lean','theorem cap')], [('ch2',27,'section 7, (7.16), low-ordinate input'),('ch2',43,'Lemma B.1')])

add('P04','Two-range zero count: the written +.332 improvement is sound','accepted-written',
 'PNT.md’s final section replaces the single coarse low-sum estimate with a two-range count calculation. It explicitly labels A+.332 as written, not as PNTClosed.sharpened’s compiled conclusion.',
 'CH2 Lemma B.1 states |N(t)−M(t)|<1 for 0<t≤280 and |N(t)−M(t)|≤(log t)/5+2 for t≥1. Counts are 0<γ≤t, with multiplicity. The source’s main term is:',
 [r'M(t)=\frac t{2\pi}\left(\log\frac t{2\pi}-1\right)+\frac78.',
 r'a=2\pi,\ b=280,\ H=20000,\quad N(a)=0,\qquad2\sum_{0<\gamma\le H}\frac1\gamma=\frac{2N(H)}H+2\int_a^H\frac{N(t)}{t^2}\,dt.',
 r'2\sum_{0<\gamma\le H}\frac1\gamma\le\frac{\log^2(H/a)}a+\frac7{4a}+\frac2b\left(\frac{\log b}5+\frac65\right)-\frac2{5H}<10.651.',
 r'10.651-10.3194=.3316<.332.'],
 'The main term contributes log²(H/a)/a+2M(a)/a, where M(a)=−1/8. The two error integrals contribute 2/a+(2/b)(log b/5+6/5)−2/(5H). Combining the −1/(4a) with 2/a gives 7/(4a), so the signs and endpoint terms agree. An atom at H is already included by the N(H)/H boundary term. The source input is applied on its complete small range, rather than only at a. Using log(H/a)<8.066, π>3.141592 and log280<6 verifies the final cap.',
 'Accepted mathematical refinement through the same additive spectral mechanism. It remains a written variant; the supplied compiled endpoint stays A+.821.',
 [('PNT.md','### Two-range RvM variant')], [('ch2',43,'Lemma B.1'),('ch2',27,'section 7, (7.16)')])

add('P05','Signed θ relay and π transfer retain their admitted domains','accepted-written-and-conditional',
 'ThetaSigned.signed_psi_to_theta proves the .99/1.01 square relay on the actual Mathlib Chebyshev functions, with RH and the Büthe finite-height ψ predicate. The J-to-π integral argument is supplied in PNT.md as written mathematics.',
 'Büthe 2016 Theorem 2 gives the Schoenfeld-scale bounds under 4.92√(x/log x)≤T. Full RH supplies any such T. Büthe 2018 Theorem 2 (1.5),(1.8) supplies the finite anchor. GM Theorem 1.1 supplies the integral primitive below.',
 [r'.99\sqrt x\le\psi(x)-\vartheta(x)\le1.01\sqrt x\qquad(x\ge e^{34}).',
 r'J(x)=\sum_{k\ge1}\frac{\pi(x^{1/k})}k,\quad r=\psi(x)-x,\qquad |J(x)-\operatorname{li}(x)-r/L|\le14+.278\sqrt x/L^2.',
 r'.99\le\frac{L(J(x)-\pi(x))}{\sqrt x}\le1.10,',
 r'\frac rL-\frac{1.10\sqrt x}L-C(x)\le\pi(x)-\operatorname{li}(x)\le\frac rL-\frac{.99\sqrt x}L+C(x),\quad C(x)=14+.278\sqrt x/L^2.'],
 'The three roots in the upper Costa Pereira inequality use exponents 2,3,5. At L≥34 each root exceeds 59, so the exact finite-height ψ predicate is applied within its domain. The lower form has exponents 2,3,7 and nonnegative discarded terms. For the written integral, a₀=e⁸ is within Büthe’s finite range. Integration by parts with |B₀(t)|≤.0462t³ᐟ²+1.838t yields coefficient 6·.0462=.2772<.278 and anchor constant <14. The square part of J−π has upper allowance <1.071, and higher powers <.028; both are checked by their decreasing endpoint bounds. The general π(t)≤2t/log t auxiliary follows from the certified li barrier plus finite Büthe sign below 10¹⁹ and Schoenfeld above it.',
 'The signed transfer is mathematically sound and keeps the actual endpoint r. The full written J/π proof is not a new kernel proof. No unconditional Johnston endpoint is enlarged by varying T under RH.',
 [('ThetaSigned.lean','theorem signed_psi_to_theta'),('PNT.md','### Prime powers and integral transfer'),('Ramanujan.md','For the auxiliary')], [('buthe16',13,'Theorem 2, (7.1)–(7.2)'),('buthe18',2,'Theorem 2, (1.5),(1.8)'),('gm',3,'Theorem 1.1, K=Q')])

add('P06','Same-source prior bound: this is not a uniform best-bound claim','qualified',
 'PNT.md explicitly claims improvement over Lee–Nosal and records finite Büthe minima; it does not prove optimality or a complete published frontier. The new coefficient is obtained from the same CH2 corollary as an existing published RH estimate.',
 'CH2 Corollary 9.3, Eq. (9.4), PDF page 36, states the exact bound below for x>1, T=2π²√x/log x≥10⁷, and RH to height T. Full RH supplies its placement assumption.',
 [r'|\psi(x)-x|\le\frac{\sqrt x}{8\pi}\left[\left(\log x-2\log\frac{\log x}{\pi e}\right)^2-4\right].',
 r'H(L)=\frac{(L-2\log(L/(\pi e)))^2-4}{8\pi},\qquad H(34)\approx38.664061<A(34)\approx38.667767.',
 r'H(40)-A(40)>.09.'],
 'The height condition holds at L=34 and remains valid afterward. Independent exact rational-series checks show H(34)−A(34)<−.003 and H(40)−A(40)>.09. Thus the envelopes exchange relative strength near the start of the new ray; no global dominance over this already published same-source bound follows merely from the valid Lee–Nosal comparison.',
 'A remains valid and improves both correctly quoted Lee–Nosal ψ theorems on its stated ray. Credit it as an adaptive source composition and scoped coefficient refinement, not a wholly new analytic method, uniformly best published estimate, or priority claim.',
 [('PNT.md','### Variable height and pointwise comparison')], [('ch2',36,'Corollary 9.3, Eq. (9.4)')])

add('W01','Weighted primitive route: constants and normalizations agree','accepted-written',
 'Weighted.md defines endpoint-subtracted first-Mertens, reciprocal-prime, and log-product errors. Its first route assumes only the published RH primitive estimate in addition to standard normalization identities.',
 'GM v5 Theorem 1.1, PDF page 3, gives the following exact K=Q clause for every t≥3 under RH. Here ψ⁽¹⁾(t)=∫₀ᵗψ(u)du, so it gives the stated primitive of ψ(u)−u.',
 [r'B_0(t)=\int_0^t(\psi(u)-u)\,du,\qquad|B_0(t)|\le .0462t^{3/2}+1.838t\quad(t\ge3).',
 r'M_1=\sum_{p\le x}\frac{\log p}p-\log x-E,\quad M_2=\sum_{p\le x}\frac1p-\log\log x-B,\quad M_P=\log\frac{P(x)}{e^\gamma\log x},',
 r'P(x)=\prod_{p\le x}(1-1/p)^{-1},\quad E=-\gamma-\sum_p\frac{\log p}{p(p-1)},\quad B=\gamma+\sum_p\left(\log(1-1/p)+1/p\right).',
 r'T_0=\int_x^\infty\frac{\psi(t)-t}{t^2}\,dt,\quad T_1=\int_x^\infty\frac{\psi(t)-t}{t^2}\left(\frac1{\log t}+\frac1{\log^2t}\right)\,dt.',
 r'\sqrt x|T_0|\le5c+3b/\sqrt x<.232,',
 r'\sqrt xL|T_1|\le c(5+7/L+4/L^2)+b x^{-1/2}(3+4/L+2/L^2)<.241\quad(L\ge34).'],
 'Direct differentiation gives −g₁′=t⁻³(2/log t+3/log²t+2/log³t). Bounding the boundary and integral terms separately yields exactly the displayed coefficients. The limiting constants in the two Mangoldt sums are −γ and +γ respectively; the first follows from the CH2 weighted normalization, and the second from the classical Mertens product identity. With inclusive finite sums, ordinary Stieltjes summation retains the full atom at x. The E constant in M₁ includes all primes, including p>x.',
 'Accepted written derivation. The factor-3 Lee–Nosal comparison is on the common ray, not an onset improvement. The bound on the normalized product itself uses exponentiation, with |M_P|<.000002 and an explicit 1.001 allowance before rounding to 1.05.',
 [('Weighted.md','## Proof with only the primitive estimate'),('Weighted.md','For \\(M_1\\) add')], [('gm',3,'Theorem 1.1, K=Q clause'),('lee-nosal',3,'Corollary 1.3, (4)–(7)'),('lamzouri',4,'Lemma 2.3, exact identity (2.4)')])

add('W02','Exact spectral resolvent: integrating before the modulus is valid','accepted-written',
 'Weighted.md replaces separate endpoint/integral moduli with the signed primitive’s integrated zero term. No frozen Lean declaration proves that spectral integration; the prose explicitly says so.',
 'GM Eq. (1.3a), page 2, with Lemma 3.3, page 9, gives the following K=Q primitive. The completed-zeta Hadamard product and functional equation used for the mass calculation are GM (3.3)–(3.6), page 7.',
 [r'B_0(t)=-\sum_\rho\frac{t^{\rho+1}}{\rho(\rho+1)}-t\log(2\pi)+r^{\prime}-\sum_{k\ge1}\frac{t^{1-2k}}{2k(2k-1)}.',
 r'I_s(x)=\int_x^\infty(\psi(t)-t)t^{-2-s}\,dt=-\sum_\rho\frac{x^{\rho-1-s}}{\rho(1+s-\rho)}-\frac{\log(2\pi)}{(1+s)x^{1+s}}+\int_x^\infty\frac{-\log(1-t^{-2})}{2t^{2+s}}\,dt.',
 r'\mathrm{RH}:\quad|\rho(1+s-\rho)|\ge|\rho|^2,\qquad Z=\sum_\rho|\rho|^{-2}=2+\gamma-\log(4\pi)<.047.',
 r'|I_s(x)|\le .047x^{-1/2-s}+\frac{2x^{-1-s}}{1+s}\quad(s\ge0,\ x\ge3).',
 r'\sqrt x|T_0|<.048,\qquad\sqrt xL|T_1|\le .047(1+1/L)+2/\sqrt x<.049\quad(L\ge34).'],
 'For each primitive zero term, the signed boundary and integrated term combine algebraically into −1/[ρ(1+s−ρ)]; the r′ constant cancels. Absolute interchange can be justified before this cancellation: the two terms from the primitive are bounded by [1+(2+s)/(s+1/2)]x⁻¹ᐟ²⁻ˢ/|ρ(ρ+1)|, with bracket at most 5 for s≥0. Thus the convergent inverse-square mass dominates them uniformly. RH gives 1−ρ=conjugate(ρ), and |1+s−ρ|²=|ρ|²+s+s². Subtracting the completed Hadamard logarithmic derivatives at 1 and 0 gives the absolutely convergent mass; the completed function is nonzero at those points, so the zeta pole has been removed. The digamma value at 1/2 and the Laurent coefficient at 1 give 2+γ−log(4π). Elementary bounds γ<.578 and log(4π)>2.531 are independently checked. For the trivial term, −log(1−t⁻²)/2≤(9/16)t⁻², so its positive contribution is smaller than the subtracted log(2π) term. Finally, the Laplace representation of 1/log t+1/log²t permits the s integral, with absolute integrability supplied by Schoenfeld.',
 'Accepted written RH mathematics with exact source normalization and justified interchanges. It uses no numerical zero list. It remains outside the frozen Lean proof chain and is not source-first program verification.',
 [('Weighted.md','## Stronger tail route'),('Weighted.md','The **analytic** inverse-square mass')], [('gm',2,'Eq. (1.3a)'),('gm',9,'Lemma 3.3'),('gm',7,'completed product and functional equation, (3.3)–(3.6)')])

add('W03','Sharper weighted bands: prime-power corrections have the right sign','accepted-written',
 'Weighted.md claims the .942–1.094, .886–1.173 and .886–1.174 endpoint-subtracted bands. The ordinary prime and von Mangoldt sums are distinct; the full correction for M₁ and M₂ includes primes exceeding x.',
 'Lamzouri Lemma 2.3 and Eq. (2.4), page 4, gives the exact finite-product identity displayed first. It already explains the asymptotic square-induced shift. The sharper finite constants here combine that identity with the checked RH tails and Schoenfeld partial summation.',
 [r'\log\prod_{p\le x}(1-1/p)^{-1}=\sum_{n\le x}\frac{\Lambda(n)}{n\log n}+\sum_{\substack{k\ge2\\x^{1/k}<p\le x}}\frac1{kp^k}.',
 r'M_1=\frac{\psi(x)-x}x-T_0+\sum_{\substack{p,\ k\ge2\\p^k>x}}\frac{\log p}{p^k},\quad E=-\gamma-\sum_p\frac{\log p}{p(p-1)}.',
 r'.942\le\sqrt x\left(M_1-\frac{\psi(x)-x}x\right)\le1.094,',
 r'.886\le\sqrt xL\left(M_P-\frac{\psi(x)-x}{xL}\right)\le1.173,\quad .886\le\sqrt xL\left(M_2-\frac{\psi(x)-x}{xL}\right)\le1.174\quad(x\ge e^{34}).'],
 'For M₁ the square term lies in [.99,1.01] after scaling by √x, the higher-power tail costs <.035, and the spectral integral costs <.048. Hence the upper constant is at most 1.093<1.094 and the lower is .942. For the product, the square main integral is at least 1−2/L−1/(2√x); Schoenfeld costs <.006, leaving >.935. Higher powers cost <.118 and the spectral integral <.049, giving the stated .886 and 1.173. The M₂-only primes p>x cost <.001. All four tail allowances decrease on the ray; exact endpoint scalar checks are included. The product correction for k≥3 is bounded by splitting at x¹ᐟ³, preserving the first allowed exponent at each prime.',
 'Accepted as written finite-domain RH bounds. On a Büthe Table 1 row with upper ψ-deficit M≤.88, the log-product lower coefficient is at least .886−M. The 10¹⁶ row has M=.74, so .146 is valid on that closed row. This does not establish full finite-band sign coverage, and it is not the separate Root post-lock first-Mertens theorem.',
 [('Weighted.md','.942'),('Weighted.md','For a concrete signed consequence')], [('lamzouri',4,'Lemma 2.3, (2.4), Corollary 2.2'),('buthe18',14,'Table 1, row 10^16'),('schoenfeld',1,'Theorem 10, (6.2)–(6.5)')])

add('W04','Primorial margin: the conditional consumer is correctly labeled','accepted-conditional',
 'WeightedConsumer.log_primorial_margin takes arbitrary positive P, arbitrary real γ, RH, the Büthe2016 ψ predicate, and hband supplying the exact .886 weighted lower band. It proves the log-log tangent cancellation and the θ positivity. It does not derive hband or construct the primorial in Lean.',
 'The .886 band is the preceding written GM/Lamzouri consequence; the .99 square relay comes from the actual Mathlib prime-power identities and Büthe2016 source input. The two tangent inequalities below are elementary consequences of log u≤u−1 on positive u.',
 [r'\log\log\vartheta(x)-\log\log x\le\frac{\vartheta(x)-x}{x\log x},\qquad\vartheta(x)>1,',
 r'\log\frac{P(x)}{e^\gamma\log\vartheta(x)}\ge M_P-\frac{\vartheta(x)-x}{xL}\ge\frac{.886+.99}{\sqrt xL}=\frac{1.876}{\sqrt xL}.',
 r'N=\prod_{p\le x}p:\qquad\log N=\vartheta(x),\quad P(x)=N/\varphi(N).'],
 'The argument does not assume a sign for ψ(x)−x: its endpoint cancels. The Lean proof uses the exact lower relay, proves θ>1 before applying log, and expands the positive denominators. Instantiating P with the finite prime Euler product and γ with Euler’s constant gives the written primorial consequence. Those finite-product/φ identities and the source-to-hband analytic chain are not newly formalized in this consumer.',
 'Accepted conditional Lean transport and written quantitative primorial result. No claim of a new Nicolas equivalence or an RH-only formal primorial theorem is justified.',
 [('WeightedConsumer.lean','theorem log_primorial_margin'),('WeightedConsumer.lean','(hband :'),('Weighted.md','In particular the quantitative primorial')], [('gm',2,'(1.3a), via the written weighted derivation'),('lamzouri',4,'(2.4)'),('buthe16',13,'Theorem 2')])

add('I01','Signed finite counts and the local power bound are valid','accepted-written-and-conditional',
 'Intervals.buthe_count proves the first bound on actual inclusive prime counts. Intervals.md adds the 2.91√x count consequence and the Table 1 local prime-power subtraction as written mathematics.',
 'Büthe2018 Theorem 2 (1.6),(1.7) supplies the signed θ deficits; Table 1 page 14 supplies the exact ψ bands on closed rows. At b=2·10¹⁴ the row has m=−.60 and M=.76.',
 [r'\pi(y)-\pi(x)\ge\frac{y-x-1.95\sqrt y+.05\sqrt x}{\log y}\quad(1423\le x\le y\le10^{19}).',
 r'y=x+2.91\sqrt x\le10^{19},\ x\ge10^8\quad\Longrightarrow\quad\pi(y)-\pi(x)>\frac{\sqrt x}{\log x}.',
 r'\pi(y)-\pi(x)\ge\frac{y-x-M\sqrt y+m\sqrt x}{\log y}-\sum_{k=2}^{K}\left(\frac{y-x}{k^2x^{1-1/k}}+\frac1k\right),\quad K=\lfloor\log y/\log2\rfloor.',
 r'\sum_{k=2}^{K}\left(\frac{y-x}{k^2x^{1-1/k}}+\frac1k\right)\le\frac{y-x}{\sqrt x}+\log K.'],
 'The source θ difference gives the signed numerator, and each prime in (x,y] weighs at most log y; the proof uses the actual finite set difference. For the 2.91 consequence, √y≤√x+1.455 makes the numerator at least 1.01√x−2.83725, and log y≤log x+2.91/√x. The inequality .01√x>2.83725+2.91/log x holds from x=10⁸ onward. In the local power subtraction, concavity bounds the number of integers in (x¹ᐟᵏ,y¹ᐟᵏ] by 1+(y−x)/(kx¹⁻¹ᐟᵏ), while log p≤log y/k. Summing uses Σₖ≥₂1/k²<1 and Σ₂ᴷ1/k≤log K. For y=x+2.4√x in [2·10¹⁴,4·10¹⁴], the surplus over √x/log y exceeds .04√x−.912−34(2.4+4)>0.',
 'Accepted with the upper endpoint and single-row containment guards retained. These count claims are not global short-interval RH-only theorems and do not supersede stronger published finite maximal-gap data for mere existence.',
 [('Intervals.lean','theorem buthe_count'),('Intervals.md','For \\(x\\ge10^8'),('Intervals.md','### Local prime-power subtraction')], [('buthe18',2,'Theorem 2, (1.6)–(1.7)'),('buthe18',14,'Table 1, row 2·10^14')])

add('I02','DGM direct symmetric count: the .9 additive allowance is enough','accepted-written',
 'Intervals.md claims more than α√X primes in the open symmetric interval with h=((1/2+α)log X+.9)√X, for X≥exp40 and 1≤α≤2. No new frozen Lean declaration proves this spectral calculation.',
 'DGM v2 Eq. (3.1), page 5, gives the exact weighted-prime lower bound below. Its Theorem 1.1 already gives at least √X primes in the larger open interval with h=(3L/2+2)√X for every X≥2.',
 [r'\sum_{|p-X|<h}\log p\ge h-\sqrt X\log T-\frac{2\sqrt X\log T}{\pi\beta}-(3-\log(2\pi))\sqrt X-\frac{2\log(2\pi)\sqrt X}{\pi\beta}-\frac{4\sqrt X\log(T/(2\pi))}{\pi\beta^2}-3X^{1/3}',
 r'\hspace{8mm}-\left(\frac{8\log T}{\pi\beta}+\frac{\log^2T}\pi+2.05+\frac{12\log T}{\beta^2}\right)\frac h{\sqrt X}-\frac3{Xh}.',
 r'T=\frac{\sqrt X}{(1/2+\alpha)\pi},\quad\beta=hT/X\ge L/\pi,\quad h=((1/2+\alpha)L+.9)\sqrt X.',
 r'.62+.258+.004+.001+.00002=.88302<.9.'],
 'All source regime conditions hold: X>121, T>14.14 and 0<h≤X/√3. The first three zero-loss terms in √X units are at most L/2+4−log(3π²)<L/2+.62. The next two cost at most (4+2π)/L<.258; cubes cost <.004; all h terms cost at most (L²+8)3Le⁻ᴸᐟ²<.001. The endpoint change αlog(1+h/X) and last rational term each cost <.00001. Every polynomial-exponential remainder decreases from L=40. Thus the weighted sum exceeds α√X log(X+h), implying the strict unweighted count. Exceptional cutoff ordinates can be avoided by nearby T and a limit of the continuous scalar bound.',
 'Accepted written improvement of DGM’s additive width on a later ray. The source has much earlier onset, and CMS has a better asymptotic coefficient. The open symmetric endpoints are preserved.',
 [('Intervals.md','## Direct DGM RH count')], [('dgm',5,'§3, Eq. (3.1)'),('dgm',1,'Theorem 1.1')])

add('I03','CMS quantitative count: the widened parameter range was rechecked','accepted-written',
 'Intervals.md retains CMS’s interior-prime term and claims π(x+c√x log x)−π(x)>α√x for x≥4·10¹⁸, 1≤α≤2 and c=(22/25)(1+2α). In particular c=2.64 when α=1. It explicitly calls this written analysis, not a Lean CMS replay.',
 'CMS v2 Theorem 3, page 5, gives an asymptotic coefficient <(21/25)(1+2α), with no explicit onset. Its Theorem 5 gives existence in [x,x+.88√x log x] for x≥4. For the effective count extension, the exact original §6 inequalities are:',
 [r'\inf\left\{c>0:\liminf_{x\to\infty}\frac{\pi(x+c\sqrt x\log x)-\pi(x)}{\sqrt x}>\alpha\right\}<\frac{21}{25}(1+2\alpha).',
 r'\Delta\sqrt a\le\sum_\gamma|f(\gamma)|+\frac1{2\pi}\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\widehat F\!\left(\frac{\log(n/a)}{2\pi\Delta}\right)+\frac3{2\Delta}\left(\frac{e^{2\pi\Delta/\lambda}}a\right)^{5/2}\quad\text{(6.5)},',
 r'\sum_\gamma|f(\gamma)|<\frac{\log(1/(2\pi\Delta))}{2\pi}\|F\|_1+\frac{.070}{2\pi}\quad(\Delta<10^{-8})\quad\text{(6.9)},',
 r'F(t)=\frac{\cos(2\pi t/.9)}{1-16(t/.9)^2},\quad\lambda=.9,\quad\|F\|_1=.83337\ldots,\quad J(F)=\frac{1-4\int_{[-1,1]^c}\widehat F}{\|F\|_1}>\frac{25}{22}\quad\text{(6.11)},',
 r'S_{\rm out}\le8\widehat F(1)+4\sqrt a\,s\int_{[-1,1]^c}\widehat F+24\sqrt a\,s^2\widehat F(1)(.9^{-1}-1),\quad s=2\pi\Delta\quad\text{first line of (6.14)}.'],
 'The paper’s final .886 outside constant was shown only for c≤1, so it cannot simply be reused at c≤4.4. The frozen text correctly returns to the first line of (6.14): with x≥4·10¹⁸, log x<43 at the endpoint, √x≥2·10⁹, and decreasing L²e⁻ᴸᐟ², one gets Δ<10⁻⁸ and √a s²≤4.4²·43²/(4·10⁹)<10⁻⁵. Since 8F̂(1)≤.885, the extra outside term is <.001, recovering .886. Its new prime-power argument gives at most 68L²e⁻ᴸᐟ²<.001, valid also for closed support endpoints. The trivial-zero term and the possible prime at x each cost <.001. Thus the range extension is actually justified rather than assumed.',
 'Accepted effective count on the stated ray, conditional on the published Fourier and explicit Brun–Titchmarsh inequalities and their numerical test-function constants. It improves the symmetric DGM width comparison in the stated sense; it does not beat CMS Theorem 3 asymptotically or improve CMS’s existence onset.',
 [('Intervals.md','## Stronger explicit Fourier count'),('Intervals.md','For the outside primes')], [('cms',5,'Theorems 3 and 5, (1.13)'),('cms',22,'Eq. (6.5)'),('cms',24,'(6.9), (6.11)'),('cms',25,'first inequality in (6.14)')])

add('I04','CMS contradiction: endpoint counting and limiting step close','accepted-derived',
 'The final CMS paragraph assumes the desired count fails in (x,y] and derives a contradiction while retaining a possible prime at x. This is a written continuation of the original source inequality, rather than a new source attribution.',
 'CMS §6.3, Eq. (6.16), page 26, obtains the inequality without an interior-prime term under a no-primes hypothesis. Keeping that term gives the following precise extension:',
 [r'\pi(y)-\pi(x)\le\alpha\sqrt x\ \Longrightarrow\ S_{\rm in}\le\|F\|_1\alpha L+.001,\qquad y=x+c\sqrt xL.',
 r'J(F)\sqrt a\,s\le\log(1/s)+\alpha L+1.16,\qquad\frac{.070+.886+.001+.001+.001}{.83}<1.16.',
 r'\sqrt a\,s\ge cL/2-.001,\qquad\log(1/s)\le L/2-\log(c\log2\,L/2)<L/2-3.',
 r'(\alpha+1/2)L-\frac{25}{22}(.001)<J(F)\sqrt a\,s<(\alpha+1/2)L-1.84\qquad\text{(impossible)}.'],
 'There are at most α√x+1 primes in [x,y], and (log p)/√p≤L/√x because x>e². The bound |F̂|≤||F||₁ then gives the first line. The remaining error total divided by .83 is <1.16. The lower estimate for √a s follows from log(1+u)≥u−u²/2; the upper estimate for log(1/s) follows from log(1+u)≥u log2 for 0≤u≤1 and c≥2.63, L>42. The coefficient identity (25/22)c/2=α+1/2 gives the contradiction. If the Mellin parameter hits a zero ordinate, choose c′ increasing to c outside the countable exceptional set; the smaller intervals inherit the failed-count upper bound, all uniform scalar estimates hold for c′≥2.63, and then pass to the limit. This preserves the possible prime at x and the inclusive endpoint y.',
 'No missing interior-prime, cutoff, or endpoint term was found in this argument. The formal proof status remains written, as the frozen text declares.',
 [('Intervals.md','**Interior term and contradiction.**'),('Intervals.md','If \\(\\vartheta')], [('cms',26,'§6.3, Eq. (6.16) and final contradiction')])

add('S01','Baseline domain ledger and explicit exclusions','qualified',
 'The initial PNT table, weighted comparison and interval derivations use the following inherited published domains. This bounded review concerns the requested PNT, weighted, primorial and interval claims, not every declaration in the 87-file frozen package.',
 'Büthe2018 Theorem 2; Büthe2016 Theorem 2; Johnston Theorem 3.2 and Corollary 3.3; Schoenfeld Theorem 10 and Corollary 1; and Rosser–Schoenfeld1962 Theorem 12 establish:',
 [r'|x-\psi(x)|\le.94\sqrt x\ (11<x\le10^{19}),\quad .05\sqrt x<x-\vartheta(x)\le1.95\sqrt x\ (1423\le x\le10^{19}).',
 r'0<\operatorname{li}(x)-\pi(x)\le\frac{\sqrt x}{\log x}\left(1.95+\frac{3.9}{\log x}+\frac{19.5}{\log^2x}\right)\quad(2\le x\le10^{19}).',
 r'\mathrm{RH}:\quad|\psi-x|\le\frac{\sqrt x\log^2x}{8\pi}\ (x>59),\quad|\vartheta-x|\le\frac{\sqrt x\log^2x}{8\pi}\ (x>599),\quad|\pi-\operatorname{li}|\le\frac{\sqrt x\log x}{8\pi}\ (x>2657).',
 r'0\le\vartheta(x)\le\psi(x)<1.03883x\quad(x>0).',
 r'\text{Johnston: }\frac{9.06}{\log\log x}\sqrt{\frac{x}{\log x}}\le T;\quad |\pi(x)-\operatorname{li}(x)|<\frac{\sqrt x\log x}{8\pi}\quad(x\ge2657),',
 r'T=3\cdot10^{12}:\quad2657\le x\le1.101\cdot10^{26}\quad\text{(Johnston Corollary 3.3)}.'],
 'Schoenfeld’s original Corollary 1, (6.18), visibly prints 2657≤x; the frozen table’s parenthetical closed endpoint is correct. Büthe2016’s own corresponding theorem prints x>2657. These two published domains must be distinguished; no endpoint mismatch is counted. The scanned primary formula, rather than the imperfect extracted text, controls this comparison. The original Rosser–Schoenfeld PDF was independently recovered from a mirror and its Theorem 12, Eq. (3.35), printed page 71, was read; a failed earlier Project Euclid fetch is not used as evidence. The Schoenfeld scan’s printed page 339 was checked through its primary PDF/text. Full RH legally supplies all finite-height premises; it does not certify finite zero lists or source programs.',
 'No new source-domain failure was found. The two confirmed issues above concern the Lee–Nosal comparison prose. Root’s post-lock Mertens-positive theorem and both Ramanujan610/640 routes, their crossing, their source-first program claims, and Laurent.md’s coefficient-sign derivation are explicitly outside this review. Their evidence is not credited to the reviewed arm here.',
 [('PNT.md','| Quantity |'),('Weighted.md','compared with the factor 3'),('Intervals.md','Prime counts are')], [('buthe18',2,'Theorem 2, (1.5)–(1.10)'),('buthe16',13,'Theorem 2'),('johnston',4,'Theorem 3.2'),('johnston',8,'Corollary 3.3'),('schoenfeld',1,'Theorem 10'),('schoenfeld',3,'Corollary 1, (6.18)'),('rosser-schoenfeld1962',8,'Theorem 12, (3.35), printed p.71')])

result={'status':'BOUNDED_FINAL_IEANTN_MATHEMATICAL_REVIEW_COMPLETE','reviewer':'rh_neutral_adapter; independent evaluator, no worker contact',
 'frozen_root':str(FROZEN),'frozen_population_files':87,'requested_scope':'PNT adaptive ray and reduced predicates; written A+.332; weighted primitive/spectral bands and conditional primorial1.876; finite/local and direct DGM/CMS interval counts',
 'not_an_all_87_declaration_source_audit':True,'confirmed_comparison_errors':['E01','E02'],
 'main_conclusion':'Both corrected Lee–Nosal comparisons survive. No mathematical counterexample or additional unresolved analytic step was found in the requested adaptive, weighted, or interval derivations. Exact source and conditional-formal boundaries remain explicit.',
 'formal_limits':['PNTClosed retains RH and exactly eight source predicates','A+.332 is written only; compiled reduced endpoint remains A+.821','Integrated spectral weighted bands and CMS/DGM derivations are written only','WeightedConsumer retains hband and positive P, and does not construct the actual primorial'],
 'excluded':['Root post-lock MertensPositive synthesis','Ramanujan610/640 and crossings/source-first claims','Laurent.md coefficient-sign proof','global strongest-literature or novelty census','independent full inherited Lean/application replay'],
 'cards':cards}
(B/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n')
font=base64.b64encode((B/'render-support/fonts/STIXGeneral.ttf').read_bytes()).decode()
css='''@font-face{font-family:STIX;src:url(data:font/ttf;base64,FONT) format('truetype')}*{box-sizing:border-box}body{background:#edf2f6;color:#183047;font:16px/1.55 system-ui,sans-serif;margin:0;padding:15px}main{max-width:1100px;margin:auto}header,article{background:white;border:1px solid #d5e0e8;border-radius:10px;margin:13px 0;padding:21px}h1{font-size:29px;line-height:1.2}h2{font-size:22px;line-height:1.25;margin:0 0 10px}h3{font-size:15px;color:#4d667e;margin:17px 0 5px}.accepted,.accepted-derived,.accepted-written,.accepted-conditional,.accepted-written-and-conditional{border-left:7px solid #258063}.comparison-error{border-left:7px solid #bf543d}.qualified{border-left:7px solid #aa8028}.eq{padding:11px;background:#f2f6fa;border-radius:5px;margin:10px 0;overflow:auto;max-width:100%}math{font:20px STIX,serif}.status{font-size:12px;font-weight:750;letter-spacing:.07em;text-transform:uppercase}p{margin:8px 0;overflow-wrap:anywhere}a{color:#165e9a}code{font-size:13px;overflow-wrap:anywhere}.meta,footer{font-size:13px;color:#50677a}nav{display:flex;flex-wrap:wrap;gap:9px}nav a{background:#e7f0f6;padding:4px 8px;border-radius:5px}pre{white-space:pre-wrap;overflow-wrap:anywhere}.evidence{background:#f5f8fb;padding:10px;border-radius:6px}.goodtag{color:#197356}.badtag{color:#a23d29}table{border-collapse:collapse;width:100%}td,th{border-bottom:1px solid #dde5eb;padding:8px;text-align:left}@media(max-width:600px){body{padding:6px}header,article{padding:14px}h1{font-size:25px}h2{font-size:20px}math{font-size:18px}}'''.replace('FONT',font)
esc=html.escape
def a(h,t):return '<a href="'+esc(h,quote=True)+'">'+esc(t)+'</a>'
def eq(s):return '<div class="eq">'+convert(s,display='block')+'</div>'
def excerpt(s):
 parts=re.split(r'(\\\(.*?\\\))',s)
 return ''.join(convert(t[2:-2])if t.startswith('\\(')and t.endswith('\\)')else esc(t)for t in parts)
out=['<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta http-equiv="Content-Security-Policy" content="default-src \'none\'; style-src \'unsafe-inline\'; font-src data:; img-src data:"><title>Final IEANTN RH: independent mathematical review</title><style>'+css+'</style><main><header><div class="status">Independent final-arm mathematical review · 20 November 2026</div><h1>Valid adaptive, weighted and interval bounds; two comparison corrections</h1><p><strong>The reviewed main bounds survive.</strong> Lee–Nosal 1.1 is misquoted in the frozen manuscript, and the claimed global ordering of their two theorems is false. Direct comparison with the correct formulas still proves the adaptive improvement on the entire stated ray.</p><p>This is a bounded review of the requested families in the exact 87-file final IEANTN_RH snapshot. It is not an exhaustive source audit of all 87 files, a full compiler replay, or a novelty census. Root’s post-lock synthesis and the Ramanujan640 portfolio are separate and excluded.</p><p>Formal boundaries: the reduced PNT theorem retains RH and eight precise source predicates. The integrated weighted and CMS/DGM proofs are written mathematics; the Lean primorial consumer explicitly retains its weighted-band premise.</p><nav>']
for c in cards:out.append(a('#'+c['id'],c['id']))
out.append('</nav></header>')
for c in cards:
 out.append('<article id="'+c['id']+'" class="'+c['status']+'"><div class="status">'+c['id']+' · '+esc(c['status'].replace('-',' '))+'</div><h2>'+esc(c['title'])+'</h2><h3>(a) Actual manuscript, Lean and Blueprint correspondence</h3><p>'+esc(c['actual'])+'</p><p class="meta">'+esc(c['blueprint'])+'</p><div class="evidence">')
 for l in c['written_source_locations']:out.append('<p>'+a('frozen/'+l['file'],l['file']+':'+str(l['line']))+' · '+excerpt(l['fragment'])+'</p>')
 if c['id']=='E01':out.append('<p>'+a('frozen/RESEARCH_REPORT.md','RESEARCH_REPORT.md:12: corresponding PNT summary')+'</p>')
 if c['id'].startswith('P'):out.append('<p>'+a('node-statements/CH2-v1.lean','Inherited CH2.v1 node statement')+' · '+a('node-statements/ZeroCount-v1.lean','Inherited ZeroCount.v1 node statement')+'</p>')
 if c['id'] in ['W02','P03']:out.append('<p>'+a('node-statements/ZetaHadamard-v1.lean','Actual paired-Hadamard contract')+' · '+a('node-statements/ZetaLogDerivValues-v1.lean','Actual log-derivative values contract')+'</p>')
 out.append('</div><h3>(b) Exact primary source claim and locator</h3><p>'+esc(c['primary_claim'])+'</p><p>')
 out.append(' · '.join(a('sources/'+x['source']+'.pdf#page='+str(x['pdf_page']),x['source']+' PDF p.'+str(x['pdf_page'])+': '+x['locator'])for x in c['primary_locators']))
 out.append('</p>')
 for s in c['formulas']:out.append(eq(s))
 out.append('<h3>(c) Trigger, derivation and mathematical impact</h3><p>'+esc(c['analysis'])+'</p><p><strong>'+esc(c['impact'])+'</strong></p></article>')
out.append('<article class="qualified"><h2>Reproducible evidence and limits</h2><p>'+a('SCALAR_CHECKS.json','51 independent exact-rational scalar checks')+' use Machin’s formula, alternating arctangent remainders, positive exponential Taylor series and logarithm atanh series, with outward rational rounding. These validate finite constants. Whole-ray monotonicity is stated in the relevant cards; a finite check is never treated as a ray proof. These are ordinary arithmetic checks, not kernel verification or source-first PV.</p><p>'+a('PRIMARY_SOURCES.json','Original-source byte identities')+' · '+a('FROZEN_INPUT_MANIFEST.json','Exact frozen 87-file population')+' · '+a('REVIEW.json','Machine-readable scope and verdicts')+' · '+a('MISTAKES.md','Review attempt log')+'. Original PDFs are supplied locally for offline reading; source URLs and SHA256 identities are in the primary manifest.</p><p>No worker was contacted, no locked file or old job was edited, and no push occurred. The inherited module predicates stay explicit. Pole and trivial-zero terms are handled in the completed Hadamard argument and the GM explicit formula; no totalized out-of-domain definition value is counted as an issue.</p></article>')
out.append('<footer><p>Static MathML and embedded licensed STIX. No CDN, browser extension or external renderer is required.</p><details><summary>Embedded font license</summary><pre>'+esc((B/'render-support/fonts/LICENSE_STIX').read_text())+'</pre></details></footer></main></html>')
s=''.join(out)
if any(x in s for x in ['\\frac','\\(','$$']):raise RuntimeError('unrendered TeX')
(B/'REVIEW.html').write_text(s)
print(json.dumps({'html_sha256':hashlib.sha256(s.encode()).hexdigest(),'cards':len(cards),'comparison_errors':2}))
