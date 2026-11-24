#!/usr/bin/env python3
"""Emit a declaration-identity keyed matrix from the current canonical source."""
from pathlib import Path
import hashlib,json,re
S=Path(__file__).resolve().parents[1];R=S.parents[1]
D=Path('/data/ivy-rh-one-prime-20261124')
groups=[
 ('RHOnePrimeEvolution','v1','Solutions/RHOnePrimeEvolution.v1/OnePrimeNetwork.lean',[
 ('kernel_ratio_lower','Actual sine-integral quotient ≥1.14068.','No external mathematical premise.','Improves proved 1.1405 numerical checkpoint.','The Fourier/norm identification is a separate B input.'),
 ('late_open_08768','All real x≥exp44: prime in (x,x+0.8768f(x)).','CMSCosineInput.v1.obstruction + RH.v1.hypothesis + kernel_ratio_lower.','Strictly shorter than CMS 0.88 on this ray.','New CMS source premise; not a record against 2026 0.85125.'),
 ('uniform_open_08768','All real x≥exp24: prime in (x,x+0.8768f(x)).','late_open_08768 + PrimeGapTable.v1.gaps.','Extends the proved late ray, improves 0.88 width.','Historical gap-table computation not newly verified.'),
 ('finite_slab_open_08301','exp44≤x≤exp59: prime in (x,x+0.8301f(x)).','CMSCosineInput.v1.obstruction + RH.v1.hypothesis.','Preserved first checkpoint, superseded by 0.8185.','Bounded, not an asymptotic gap coefficient.'),
 ('finite_absolute_1551','exp24≤x<exp44: prime in (x,x+1551).','PrimeGapTable.v1.gaps.','Absolute-width finite bridge.','Depends on reported Nicely computation; no RH required.'),
 ('consecutive_gap_08768','Consecutive natural primes p<q, p≥exp24: q−p<0.8768f(p).','uniform_open_08768.','New strict consecutive-gap consumer of the hybrid.','The input theorem carries its original premises.'),
 ('continuous_late','All real x≥exp44: prime in (x,U(x)), U=x+2+c(log(x+1))f(x+1).','CMSCosineInput.v1.obstruction + RH.v1.hypothesis.','Whole-variable endpoint, not just one constant.','U definition and entire endpoint shift retained.'),
 ('continuous_improves_uniform','All real x≥exp44: U(x)<x+0.8768f(x).','No external mathematical premise.','Strict whole-ray endpoint comparison.','No superiority over all current literature frontiers claimed.'),
 ('continuous_uniform','All real x≥exp24: prime in (x,if x<exp44 then x+1551 else U(x)).','continuous_late + PrimeGapTable.v1.gaps.','Short finite window plus variable late frontier.','Historical finite computation stays an explicit separate input.'),
 ('bounded_open_08357','All real exp24≤x≤exp110: prime in (x,x+0.8357f(x)).','CMSCosineInput.v1.obstruction + RH.v1.hypothesis + PrimeGapTable.v1.gaps.','Numerically below 0.8358 on a bounded domain.','Does not beat an asymptotic theorem as a quantified proposition.'),
 ('bounded_open_08512','All real exp24≤x≤exp225: prime in (x,x+0.8512f(x)).','CMSCosineInput.v1.obstruction + RH.v1.hypothesis + PrimeGapTable.v1.gaps.','Below printed fixed 2026 0.85125 width on this domain.','Not a comparison with full retunings of the 2026 inequalities.'),
 ('bounded_open_08185','All real exp24≤x≤exp59: prime in (x,x+0.8185f(x)).','CMSCosineInput.v1.obstruction + RH.v1.hypothesis + PrimeGapTable.v1.gaps.','Improves earlier 0.8301/0.819 checkpoints.','Credible written 2026 retuning gives a stronger 0.8111 competitor.'),
 ]),
 ('PrimePowerPopulation','v1','Solutions/PrimePowerPopulation.v1/Solution.lean',[
 ('cube_population_all_real','All real n≥exp8: N(n³,(n+1)³)>(5.08985+1.4/logn)n√n.','PrimeInterval.v4.optimized_strict_family.','Replaces one-prime cube existence by an explicit count.','Same inherited RH+Green+Nicolas+BPT package; no new kernel.'),
 ('cube_density_all_real','All real n≥exp8: N(n³,(n+1)³)>0.70n²/logn.','PrimeInterval.v4.optimized_strict_family.','New disjoint-cell square/log scale; improves 0.648 branch.','No global prime-between-cubes record; different PNT inputs may be stronger.'),
 ('cube_density_natural','All natural n≥2981: N(n³,(n+1)³)>0.70n²/logn.','PrimeInterval.v4.optimized_strict_family.','Concrete natural onset with actual exp8<2981 proof.','No all-consecutive-squares inference.'),
 ('higher_power_population','All real n≥exp8 and natural exponent r≥3: N(n^r,(n+1)^r)>(5.08985+4.2/(rlogn))√(n^r).','PrimeInterval.v4.optimized_strict_family.','Actual counts for every integer exponent ≥3.','Not a theorem for arbitrary real r>2.'),
 ('cube_frontier','All real n≥exp8: count exceeds max(one-window count,0.70n²/logn).','PrimeInterval.v4.optimized_strict_family.','Retains small-n branch and stronger large-n density.','No branch deleted; onset unchanged.'),
 ('density_improves_648','All real n≥exp8: 0.648n²/logn<0.70n²/logn.','No external mathematical premise.','Strict same-domain density comparison.','This scalar comparison alone is not a prime theorem.'),
 ]),
 ('Goldbach','v3','Solutions/RHOnePrimeEvolution.v1/frontier/GoldbachV3Consumer.lean',[
 ('sorted_count_extended','All natural H,n with finite binary Goldbach through H, Odd n,3H≤2n, u=n−H≥exp24,C*u^0.5*logu≤H−4: sortedTriples(n)>(1/2+2.1/logu)√u, C=2.14891875.','PrimeInterval.v4.optimized_strict_family.','New range 3H≤2n with sorting-fiber bound two instead of injectivity.','Finite binary Goldbach and width/onset explicit; equality n=2H adds no odd cases.'),
 ('sorted_count_full_finite_range','All natural H,n with finite binary Goldbach through H, Odd n,u=n−H≥exp24,C√u logu≤H−4: sortedTriples(n)>(1/3+1.4/logu)√u.','PrimeInterval.v4.optimized_strict_family.','Removes n/H ratio requirement by sorting-fiber bound three.','Not a proof of binary Goldbach or an RH-only ternary computation.'),
 ('sorted_count_750m_band','Finite binary Goldbach through 4e18 implies >750000000 sorted triples for every odd natural 6e18≤n≤8e18.','PrimeInterval.v4.optimized_strict_family.','Nonempty new band excluded by old n>8e18 injective route.','No new source-first proof of the finite binary input.'),
 ]),
 ('PrimeQuantile','v4','Solutions/RHOnePrimeEvolution.v1/frontier/PrimeQuantileV4Consumer.lean',[
 ('strict_generic_block','Every C∈[1.03,16], real x≥exp24 and natural m≤(8C/9−.91015+4.2/logx)√x: x<p_{π(x)+m}<x+Cf(x), zero-based primes.','PrimeInterval.v4.optimized_strict_family.','Full exact count margin and strict upper endpoint.','Zero-based indexing, floor of real x, and m≤margin retained.'),
 ('strict_special_block','Real x≥exp24, natural m≤(180173/180000+5.8/logx)√x: x<p_{π(x)+m}<x+2.15f(x).','PrimeInterval.v4.optimized_strict_215.','Preserves stronger specialized residual and opens upper endpoint.','Specialized count not replaced by weaker generic 4.2 term.'),
 ('shifted_sqrt_block','Real x≥exp24, natural m≤√x: x<p_{π(x)+m}<x+2.14891875f(x)−4.725√x.','PrimeInterval.v4.optimized_strict_family.','Strictly shorter by exactly4.725√x at same index targets.','Fixed-x width saving, not an optimized finite H at fixed n.'),
 ])]


groups.extend([
 ('GaussianFourierWitness','v1','Solutions/RHOnePrimeEvolution.v1/gaussian_gap/GaussianNumericalWitness.lean',[
 ('integral_fourier_witness','There exist actual real F,G: Eligible F G (even/continuous/L1/nonzero/true Mathlib Fourier equality); full mass≤.74899, full positive exterior leakage≤.031152, F(0)≥.999999999.','No external mathematical premise.','Actual whole-function Fourier/numerical witness, stronger verification than the historical external ratio alone.','Kernel D, not source-first PV; the tighter .834009631 search estimate remains E.'),
 ('objective_witness','There exist Eligible F,G with positive denominator F(0)−(36/11)leak and inverse objective≤.834021.','GaussianFourierWitness.v1.integral_fourier_witness.','Derives the objective from all three genuine integral/origin enclosures.','The witness is actual functions, not unverified scalar outputs.'),
 ]),
 ('RHAsymptoticGaussian','v1','Solutions/RHOnePrimeEvolution.v1/gaussian_gap/GaussianCanonicalConsumers.lean',[
 ('normalized_gap','For every real ε>0, eventually in natural n: (p[n+1]−p[n])/(√p[n] logp[n])≤.834021+ε; p[0]=2.','CMSFunctionalInput.v1.gap_reduction + RH.v1.hypothesis + GaussianFourierWitness.v1.objective_witness.','Smaller than the fixed printed2026 asymptotic coefficient .834050619151.','No explicit onset; published CMS analytic reduction is still explicit B.'),
 ('gap_below_printed_2026','Eventually in natural n: normalizedGap(n)<.834050619151.','RHAsymptoticGaussian.v1.normalized_gap.','Strict eventual comparison, using half the positive coefficient difference as ε.','Not a global best-known-result or optimality claim.'),
 ('population_curve','Every α≥0 and ε>0: c=.834021(1+2α)+ε is positive and has a positive eventual normalized half-open count reserve above α.','CMSFunctionalInput.v1.population_reduction + RH.v1.hypothesis + GaussianFourierWitness.v1.objective_witness.','Strictly smaller displayed curve than oldCPJ .8358(1+2α).','No infimum attainment; does not dominate all2026population curves; right endpoint included.'),
 ('population_count','Every α≥0 and ε>0, eventually in real x: π(x+(.834021(1+2α)+ε)√xlogx)−π(x)>α√x.','RHAsymptoticGaussian.v1.population_curve.','Actual prime-count consumer of the same numerical witness.','No explicit real onset; half-open (x,x+width] source count, not the old strict-open N.'),
 ])
])

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for family,version,proofpath,entries in groups:
 cp=f'IEANTN/Nodes/{family}/{version}/Conclusions.lean';ct=(R/cp).read_text();pt=(R/proofpath).read_text()
 for name,statement,assumptions,baseline,limits in entries:
  token='def '+name+' : Prop :=';offset=ct.index(token);line=ct[:offset].count('\n')+1
  end=ct.find('\n\n',offset);decl=ct[offset:end if end>=0 else None].split('\nend ')[0]
  match=re.search(r'^(?:theorem|lemma) challenge_'+re.escape(name)+r'\b.*?:=',pt,re.M|re.S)
  if match is None:raise RuntimeError('Actual proof declaration missing: '+family+'.'+name)
  pline=pt[:match.start()].count('\n')+1
  rows.append({'file':cp,'declaration':family+'.'+version+'.'+name,'line':line,'source_sha256':sha(R/cp),'proof_file':proofpath,'proof_declaration':family+'.'+version+'.challenge_'+name,'proof_line':pline,'proof_sha256':sha(R/proofpath),'statement':statement,'antecedents':assumptions,'baseline_comparison':baseline,'limitation':limits,'exact_definition':decl,'exact_proof_header':match.group(0),'source_first_PV':False})
if len(rows)!=30 or len({(x['file'],x['declaration'],x['line']) for x in rows})!=30:raise RuntimeError('Headline identity count mismatch')
(S/'HEADLINE_MATRIX.json').write_text(json.dumps({'scope':'All30def declarations in the six new proved canonical node versions, not a global IEANTN source-claim census. Three external-input node versions are listed separately.','rows':rows},indent=2,ensure_ascii=False)+'\n')
verification=D/'relocated-reproduction-v2/run/compile/EXECUTION.json';audit=D/'relocated-reproduction-v2/run/audit/RESULT.json'
status=json.loads(verification.read_text())['status'] if verification.exists() else 'Final fresh compilation pending.'
lines=['# One-prime and network theorem matrix','',
'Universe: exactly all 30 conclusion definitions in RHOnePrimeEvolution.v1 (12), PrimePowerPopulation.v1 (6), Goldbach.v3 (3), PrimeQuantile.v4 (3), GaussianFourierWitness.v1 (2), and RHAsymptoticGaussian.v1 (4). This is not a global IEANTN audit. Each identity is keyed by file, declaration, and physical LF line. Exact Lean definitions and proof headers follow the table.','',
'Notation: f(x)=√x log x; N(a,b) counts natural primes with BOTH real endpoints excluded. Prime indices start at zero. U(x)=x+2+c(log(x+1))f(x+1), where c(L)=[1−2(log(.399L)−1.17)/L]/1.14068+1/(10000L).','',
'Numerical status for the selected final proof chains: D, Lean kernel checking; allowed standard axioms propext, Classical.choice, Quot.sound, no native execution axiom. Original30-row study combines the passing relocated300-source frontier/consumer closure with the passing fresh53-source Gaussian/Fourier/ANT closure; exact final receipts are preserved separately. Frontier fresh build: '+status+'. Independent final-object audit: '+('see evidence/integration-review/fresh-v1/RESULT.json' if audit.exists() else 'pending at this draft')+'. Source-first PV: NO for every row. External numerical searches are E and supply no antecedent to any row. No row is a Mathlib-RH-only theorem unless its displayed assumptions are elementary-only.','',
'Exact source premises: CMS v2 §6.3 equation (6.16), including the disclosed entire/removable extension and Fourier/L1 identification ([primary](https://arxiv.org/pdf/1708.04122v2#page=26)); historical Nicely 2019 consecutive gaps below2^64, not a new verification; and the unchanged Green/Nicolas/BPT predicates from the frozen3539bbba package. The first four consumer versions inherit that package through PrimeInterval.v4; the new Gaussian gap and population results instead use the general CMS Theorem3/Corollary4 functional inputs. Exact rendered source correspondence is gaussian_gap/SOURCE_LEDGER.html. Source URLs/version/hash manifest is sources/DOWNLOADS.json; complete source audit notes are in integration_review/ and powers/*REVIEW.json.','',
'| Actual declaration identity | Exact quantified target (see source definition below) | Antecedents consumed by proof | Baseline / strict comparison | Numerical / PV / receipt | Confidence limitation |','|---|---|---|---|---|---|']
for x in rows:
 label=x['declaration'];identity=f"[{label}](../../{x['file']}#L{x['line']}) · {x['file']}:{x['line']}"
 lines.append('| '+' | '.join([identity,x['statement'],x['antecedents'],x['baseline_comparison'],'D / no source-first PV / relocated300/24headlines; fresh53/6newheadlines +11root audit',x['limitation']])+' |')
lines+=['','## Exact declarations and actual proof headers','', 'These are extracted from the pinned current sources; the proof headers expose the typed canonical input edges. Analytic input provenance is not erased by the short canonical names.','']
for x in rows:lines+=['### '+x['declaration'],'',f"Conclusion: `{x['file']}:{x['line']}`, SHA-256 `{x['source_sha256']}`. Proof: `{x['proof_file']}:{x['proof_line']}`, SHA-256 `{x['proof_sha256']}`.",'','```lean',x['exact_definition'],'',x['exact_proof_header'],'```','']
lines+=['## Separate external input nodes','', '- CMSCosineInput.v1.obstruction: the named CMS analytic no-prime inequality; B, literature-backed, not newly proved in Mathlib. The equation/entire-extension qualification is documented in analytic/SOURCE_REMOVABLE_EXTENSION.md.', '- PrimeGapTable.v1.gaps: reported historical gap computation below2^64 with maximal gap1550; asserted input, not kernel-verified nor source-first PV. Only the new consequence and terminal-prime proof are D.', '- CMSFunctionalInput.v1.gap_reduction and population_reduction: universal numerical-free CMS Corollary4/Theorem3 consequences, using actual Fourier optimization(1.3) and B≤36/11(1.12). B, not fully formalized from Mathlib RH; no requested coefficient or Gaussian occurs in the input.', '', '## Additional proved comparison/support lemmas','', '- Actual sine integral and sharper quotient: comparisons/CMSKernelNumerics.lean, analytic/CMSJSharper.lean.', '- TerminalPrime.lean:3Lucas certificates, Std3. No empty-axiom claim.', '- PopulationFrontier.lean: exact α tradeoff, strict limiting ε margin, shifted width, actual prime-index conversion.', '- WholePopulationComparison2026.lean: exact comparison with the two PRINTED 2026 curves; not global population optimality. RetunedPublishedScalar.lean: conservative scalar positivity for all44≤L≤60; not the complete retuned prime theorem.', '- Lee2023LiteralRow.lean: negative literal Table4 right side in each written version at exp10. This does not prove a corrected prime bound.', '', '## Non-theorem experiments and negative results','', 'The loose degree12/physical-degree24 Gaussian objective≤.834021, actual Fourier equality and both ANT consumers are now kernel proved. The tighter degree12 search estimate, directed degree40/hat enclosures, failedSOS attempts, and possible further extensions of2026population comparisons remain external E or written proposals. No experiment row is silently promoted to a verified numerical node. The full-function2026retuning and Lee2026wide-window estimate prevent a global winner claim. No new Ramanujan experiment or causal exposure conclusion is part of this campaign.','']
(S/'ONE_PRIME_AND_NETWORK_THEOREM_MATRIX.md').write_text('\n'.join(lines))
print('Matrix generated:',len(rows),'written identities')
