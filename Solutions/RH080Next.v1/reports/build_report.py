#!/usr/bin/env python3
"""Build one self-contained reading report from reviewed public result data.

MathML and embedded STIX fonts need no network or JavaScript. This renderer
makes no mathematical acceptance decisions; the supplied result data retain
proof/evidence status. Use the separate strict proof validators first.
"""
import argparse,base64,hashlib,html,json,os,tempfile
from pathlib import Path
from latex2mathml.converter import convert

def esc(x):return html.escape(str(x),quote=True)
def m(tex,block=False):
 value=convert(tex,display='block'if block else'inline')
 return '<div class="formula">'+value+'</div>'if block else value

def link(text,url):return '<a href="'+esc(url)+'">'+esc(text)+'</a>'
def table(head,rows):return '<div class="table-scroll" tabindex="0"><table><thead><tr>'+''.join('<th>'+h+'</th>'for h in head)+'</tr></thead><tbody>'+''.join('<tr>'+''.join('<td>'+str(x)+'</td>'for x in r)+'</tr>'for r in rows)+'</tbody></table></div>'
def card(title,body,tone='proved'):return '<article class="card '+tone+'"><h3>'+title+'</h3>'+body+'</article>'
def p(text):return '<p>'+text+'</p>'
def details(title,body):return '<details><summary>'+title+'</summary>'+body+'</details>'

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--data',required=True,type=Path);ap.add_argument('--out',required=True,type=Path);ap.add_argument('--font',required=True,type=Path);ap.add_argument('--allow-incomplete',action='store_true');a=ap.parse_args()
 data=json.loads(a.data.read_text());complete=data['completion']['complete']
 if not complete and not a.allow_incomplete:raise ValueError('Incomplete campaign; explicit draft flag required')
 if a.out.exists():raise ValueError('Fresh output required')
 root='https://github.com/hs-chae/IEANTN_test/blob/'+data['source_commit']+'/'
 def source(path,decl=None,line=None):return link(decl or Path(path).name,root+path+('#L'+str(line)if line else''))
 cms='https://arxiv.org/pdf/1708.04122v2';br='https://zenodo.org/records/24429650/files/prime-gaps-v2.pdf';lee='https://arxiv.org/html/2403.11814v4'
 q=r'\frac{20582561296}{24680948495}'
 intro=p('A conditional number-theory and program-verification study. RH is a hypothesis throughout the prime theorems. Published analytic inputs remain named hypotheses unless their proofs are explicitly supplied here.')
 intro+=p('Source checkpoint '+link(data['source_commit'][:12],root.rstrip('/'))+'. Original 20+8 trial outcomes and all 16 new primary statuses are preserved. This report is one offline file; source, exact receipts and regeneration commands are in the accompanying bundle.')
 if not complete:intro=card('Work remains',p('This is a draft. '+esc('; '.join(data['completion']['remaining']))),'pending')+intro
 sections=[]
 lead=[]
 for row in data['leaderboard']:
  lead.append([esc(row['result']),m(row['formula']),esc(row['domain']),esc(row['verification']),esc(row['premises']),source(row['file'],row['declaration'],row.get('line'))])
 sections.append(('results','What is proved',p('A lower coefficient means a shorter interval only when the ranges, endpoint rules and hypotheses match. Eventual statements have no explicit numerical onset. Functional lower bounds constrain the Fourier method; they are not lower bounds for actual prime gaps.')+table(['Result','Exact claim or coefficient','Range / endpoints','Verification','Additional inputs','Lean declaration'],lead)))
 A=p('The comparison uses the full continuous, real, even '+m(r'L^1(\mathbb R)')+' CMS class with genuine Fourier transform '+m(r'\widehat F(t)=\int_{\mathbb R}F(x)e^{-2\pi ixt}\,dx')+'. The positive exterior leakage must be integrable, and the denominator below must be positive. Integrability of the entire Fourier transform is not assumed.')
 A+=m(r'Q_A(F)=\frac{\|F\|_1}{F(0)-A\int_{|t|>1}\max(0,\widehat F(t))\,dt},\qquad A=\frac{36}{11}',True)
 A+=p('Abel-regularized Fourier inversion proves weak duality in that larger class. This closes the earlier class restriction in the source-first C obstruction. A nonnegative combination of the same window budgets retains a common obstruction; that argument does not exclude genuinely different RH reductions. '+link('CMS(1.3), (1.12)–(1.14)',cms)+'.')
 A+=table(['Tier','Lower bound for '+m(r'Q_{36/11}')+' / upper witness','What it establishes'],[
 ['Source-first C + Lean',m(r'Q_{36/11}\ge100/123\approx0.813008'), 'Full CMS class; already excludes0.8 within this functional.'],
 ['Published dual, source checked',m(r'Q_{36/11}\ge50000/60393\approx0.827911'),'BR v2 Theorem4; not a new Lean numerical certificate.'],
 ['New directed-interval dual',m(r'Q_{36/11}\ge2000/2399\approx0.833681'),'Two actual Arb algorithms, including non-FFT complex Horner; outside Lean and source-first PV.'],
 ['Kernel-proved Gaussian witness',m(r'Q_{36/11}(F)\le'+q+r'<0.833945313'),'Degree 80, dilation 5/4, exact transform and 1124 integral cells. Eventual RH consequence only.']])
 A+=p('The strongest new numerical primal–dual enclosure has width about0.000264612. Its lower endpoint is externally interval-verified, while the kernel/source-first lower endpoint remains 100/123. These verification levels must not be merged. At leakage penalty4, the separate native dual floor is5000/5877; it does not replace the 36/11 result.')
 A+=p('The campaign screened Gaussian–Laguerre degrees/scales, rational exponential–Laguerre families, translated Gaussians, compact affine spectra and population objectives. Negative searches and timed-out LP runs are retained. No valid eventual coefficient below 0.8, optimizer convergence, optimality, or global best-known claim emerged. Changing a diagnostic penalty without proving a new RH reduction would not solve the problem.')
 sections.append(('frontier','The primal–dual frontier',A))
 B=p('The finite norm uses131,072 FFT nodes; the whole-ray witness uses16,777,216. The original affine data, meshes, signs, upward rounding and outputs are fixed. In particular the support-seven witness is not normalized by silently replacing its actual '+m(r'F(0)')+' with1.')
 B+=p('Write the even affine window as the linear interpolation of its exact nodes '+m(r'W(j/m)=a_{|j|}')+', with '+m(r'a_N=0')+' and zero outside its support. The notation is fixed by:')
 B+=m(r'P(t)=a_0+2\sum_{j=1}^{N-1}a_j\cos(2\pi jt),\quad \operatorname{sinc}(t)=\frac{\sin(\pi t)}{\pi t},\quad \operatorname{sinc}(0)=1',True)
 B+=m(r'F(u)=m^{-1}\operatorname{sinc}^{2}(u/m)P(u/m),\qquad \|F\|_1=\int_0^1|P(y)|\,dy',True)
 B+=p(link('BR v2 Lemma 5, Eq (4), p3',br+'#page=3')+' states the displayed identity at support radius 5. The formal extension for the actual radius 7 data uses proved dilation and a mesh change from 360 to 504. The entire/strip, derivative variation, prime-power, wing and endpoint estimates are proved for the actual finite affine window. A new support-seven source axiom is not introduced.')
 B+=card('A closed analytic gap',p('The earlier general weighted-zero rule was broader than the test-function specialization printed after CMS Lemma 9. It is now an ordinary Lean theorem, consumed by the final prime theorems. The published zero-count estimate remains an explicit input; the extension is proved rather than attributed to an unprinted universal source theorem.'))
 B+=p('Here the zeros are the actual nontrivial zeta zeros, counted with multiplicity.')
 B+=p('The proved declaration is '+source('Solutions/RH080Next.v1/explicit/ExplicitCMSZeroKernel.lean','cms_zero_partial_summation_kernel')+'; its exact canonical correspondence is '+source('IEANTN/Nodes/CMSExplicitInputs/v1/Conclusions.lean','CMSExplicitInputs.v1.zero_partial_summation',49)+'. The printed calculation selects a particular test function. Applying that display to every even differentiable function satisfying the stated tail conditions was the extra obligation:')
 B+=m(r'F(x)=H(x/\lambda),\qquad H(x)=\frac{\cos(2\pi x)}{1-16x^2}\quad\text{(removable values at }x=\pm1/4\text{)}',True)
 B+=m(r'N(T)=\sum_{0<\gamma\le T}\operatorname{mult}(\gamma),\quad Q(T)=\frac{T}{2\pi}\log\frac{T}{2\pi e}+\frac78,\quad |N(T)-Q(T)|\le0.15\log T+3\ (T\ge e)',True)
 B+=p(link('CMS §6.1, Lemma9 and following display, pp23–24',cms+'#page=23')+'. The proof uses the actual right-closed count, derives countable support and summability, and performs finite-cutoff FTC/Fubini before taking any infinite limit. It also proves the exact base root and handles the negative and real-zero contributions.')
 B+=m(r'g_\varepsilon(t)=\sqrt{F(t)^2+\varepsilon^2},\qquad |g_\varepsilon^\prime(t)|\le|F^\prime(t)|,\qquad 0\le g_\varepsilon(t)-|F(t)|\le\varepsilon',True)
 B+=p('Smooth modulus approximation avoids assuming that the absolute value of a differentiable function is differentiable at its zeros. The smoothing parameter tends to zero at fixed cutoff first; the cutoff then tends to infinity. Complex zeta conjugation and multiplicity preservation supply the negative-ordinate reindexing. These are mathematical proofs, not numerical checks.')
 B+=p('The signed logarithmic moment keeps its negative central contribution at '+m(r'\tau=3/8')+'. The middle contribution on '+m(r'[\tau,1]')+' is nonpositive; the positive tail is bounded by derivative variation. This is sign information in the density correction, not cancellation between different complex zeros. The finite slab uses Montgomery–Vaughan block choice16, the ray uses1, and both retain the original0.0012 error reserve.')
 B+=p('Concavity and endpoint inequalities control the complete log slab; monotonicity controls the infinite ray. Bounds on actual prime counts leave room to discard a possible upper-endpoint prime. Direct cases at4,5,7,11 and the historical CMS (1.15) finite gap input bridge the small range; the latter is explicitly literature/computation-backed, not reverified by a new giant prime search.')
 sections.append(('explicit','Why the explicit bounds are valid',B))
 C=p('Here “PV” means source-first program verification: actual external source text, an independently specified restricted syntax, execution correctness, the numerical mathematical specification, and real consumption by the ANT theorem. A kernel-only trace certificate or physical execution alone is not PV.')
 C+=m(r'\text{C source}\ \longrightarrow\ \text{independent syntax/AST}\ \longrightarrow\ \text{actual modeled main}\ \longrightarrow\ \text{output and integral bound}\ \longrightarrow\ \text{prime theorem}',True)
 C+=p('The source-verified programs are the actual recursive C ports '+source('Solutions/RH080Next.v1/pv/fft/fap_fft_recursive.c')+' and '+source('Solutions/RH080Next.v1/pv/fft/w4_fft_recursive.c')+'. They implement a mathematically equivalent recursive traversal of the original fixed-point FFT; this verifies those C bytes, not the original Python bytes. The legacy iterative C ports remain separate artifacts.')
 C+=table(['Component','Proved application obligation'],[
 ['Syntax','Actual source characters match the independently specified restricted grammar and AST, including precedence, casts, declarations and control flow.'],
 ['Arithmetic / memory','Signed fixed-point base 10⁹ limbs at scale 10³⁶; actual 25-word products, signed rounding, canonical digits, bounds, allocation, non-aliasing, scope and lifetimes.'],
 ['Full algorithm','Actual input/root initialization, all recursive calls and butterflies, all argument orders, complete twiddle recurrence, absolute-value accumulation, quadrature and upward normalization.'],
 ['Entry point / output','Actual main calls the norm function, casts its result, invokes printf, returns int0 and leaves scope. The output value is recovered from the last actual successful printf event.'],
 ['Failures','Allocation failure requests the real UINT64_MAX sentinel. Printf can return a negative int after a prefix; preserved main still returns0. Successful I/O is not assumed for every execution.'],
 ['Mathematics','Exact source-derived integer output bounds the real periodic/whole-line integral and is used by the selected ANT proof.']])
 C+=p('Generic pinned C compiler/runtime/ABI, calloc/free and stdio contracts, normal-main buffering/flush, OS delivery and hardware remain trusted. Logical stdio success can precede physical delivery. The application’s initialization, desired result or “successful effects” are not generic platform assumptions. This is not a proof of every ISO C behavior or of the compiler itself.')
 C+=m(r'\text{Fap output}=781796015790084776,\qquad \text{W4 output}=7813568381279800',True)
 C+=p('All 24 compiled observations—two programs, O0/O2/O3/UBSan, Python normal/−O/−OO harness modes—match those integers. Exact source/compiler/binary/log/time associations and42 mutation rejections are retained. These observations corroborate the model; they do not constitute its proof. Per-run peak RSS was at most 3,934,928 KiB; completed cgroup OOM counters for these physical runs were not retained, so no zero-counter claim is inferred.')
 C+=p('Matched kernel-FFT controls use the same numerical facts and analytic inputs. They prove the same prime coefficients. The extra FFT source verification closes program provenance and modeled-execution trust gaps; it does not by itself cause a stronger mathematical bound. Common scalar-provider proofs remain shared where explicitly recorded.')
 sections.append(('pv','Actual C source-first verification',C))
 D=p('Population strength differs from a one-prime coefficient. The formal convention counts primes in the half-open interval; positive limiting margin also absorbs the loss of one endpoint prime asymptotically.')
 D+=m(r'\operatorname{GoodCoefficient}(\alpha,c)\iff c>0\ \land\ \exists\delta>0\ \forall x\text{ sufficiently large}:\quad \frac{\pi(x+c\sqrt{x}\log x)-\pi(x)}{\sqrt{x}}\ge\alpha+\delta',True)
 D+=m(r'g(\alpha)='+q+r'(1+2\alpha),\quad w(\alpha)=0.851061745+1.505657839\alpha',True)
 D+=m(r's(\alpha)=0.944247+1.163388\alpha,\qquad f(\alpha)=\frac98+\frac{16}{15}\alpha',True)
 D+=p('The Gaussian route gives every coefficient '+m(r'g(\alpha)+\varepsilon')+' with '+m(r'\varepsilon>0')+'; it does not assert endpoint membership. The sparse and flat source-first 16-node programs give the displayed attained good coefficients. The radius-seven route has a strictly smaller good coefficient than its recorded line. All population statements here are eventual; the old explicit onset '+m(r'e^{24}')+' is not inherited.')
 D+=p('Taking the best available curve is a mathematical comparison, not a new primary exposure score. The report-only exact algebra places switches near 0.1055054,0.2722567 and1.8688018. At density 0.2 the radius-seven curve can strengthen the prior three-curve envelope. At density 1 the sparse width 2.107635 improves the old octic width 2.14891875; the radius-seven line is not the winner there.')
 D+=p('The published BR v2 population comparator has two lines; neither may be omitted when judging improvement. '+link('BR v2 Theorem2, p2',br+'#page=2')+'. Its modulus-one specialization uses ordinary RH; its general arithmetic-progression statement has GRH and a vanishing-family condition.')
 D+=m(r'C(\alpha)<\min\{0.851127043+1.505827\alpha,\;0.85124642+1.505237\alpha\}',True)
 D+=p('Lee supplies a stronger comparison for sufficiently large fixed populations. The exact primary statement is for RH, '+m(r'x\ge e^{20}')+' and '+m(r'\sqrt{x}\log x\le h\le x^{3/4}')+'. '+link('Lee2403.11814v4 Theorem1.1, Eqs(2),(4)',lee+'#S1.E2')+'.')
 D+=m(r'|\theta(x+h)-\theta(x)-h|<\left[\frac1\pi\log\frac{h}{\sqrt{x}\log x}+L+\frac{1.046}{\log x}\right]\sqrt{x}\log x',True)
 D+=m(r'L=\frac{2}{\pi+\sqrt{\pi^2+4\pi}}+\frac1\pi\left[2+\log\frac{\pi(\pi+\sqrt{\pi^2+4\pi}+2)}4\right]\approx1.542627287776',True)
 D+=p('For fixed '+m(r'h=c\sqrt{x}\log x')+' with '+m(r'c\ge1')+', divide the lower theta count by '+m(r'\log(x+h)')+' and let '+m(r'x\to\infty')+'. Removing an endpoint costs at most one prime. This gives the following written comparison, not an extra Lean result:')
 D+=m(r'\liminf_{x\to\infty}\frac{\pi(x+c\sqrt{x}\log x)-\pi(x)}{\sqrt{x}}\ \ge\ c-\frac{\log c}{\pi}-L',True)
 D+=p('At fixed widths 3 and 5 this gives approximately1.107674 and2.945073, below the new rounded capacities 1.767040 and 3.6328125. Conversely the flat line eventually loses to this Lee consequence: the report-only high-precision crossover is near density 21.436663. There is no assertion of dominance for every population, a best-known result or optimality.')
 if data.get('population_figure_svg'):
  svg=data['population_figure_svg'];svg=svg[svg.index('<svg'):]
  D+='<figure class="scientific-figure">'+svg+'<figcaption>Illustration from exact curve coefficients; the Lee curve uses native high-precision arithmetic. This figure is not a numerical proof. On a phone, scroll the chart horizontally to read its labels. Threshold curves do not assert endpoint membership.</figcaption></figure>'
 sections.append(('population','Population gains and strong comparators',D))
 E=p('The new study has 16 sessions: four arms, two tasks, two replicates, balanced order with seed 20261126080. It is a posthoc-selected prospective transfer study, not blind discovery: the coordinator knew the input curves. Original 20+8 outcomes are a separate immutable study.')
 E+=table(['Arm','Actual mathematical/tool exposure'],[
 ['A flat','Same frozen source corpus and all selected statement types/ordinary definitions as text; no application proof objects.'],
 ['B named','143 compiled modules, named lemmas, no authored graph/source navigation. Compiled logical dependency/proof-term introspection remained possible.'],
 ['C network','Same143 modules, linked theorem graph and source navigation.'],
 ['D source-first','168 modules, adding 25 genuinely completed proofs of the two 16-node C population programs. The then-unfinished large FFT was not exposed as PV.']])
 E+=p('All arms received the same 169-module mathematical fact packet,9,371 declaration types including6,689 proof statements and2,469 ordinary nonproof definitions, and the same two C sources. Proof bodies were omitted from the flat packet; ordinary definitions could contain proof subterms identically in every arm. This is an exact selected-module scope, not an exhaustive source-claim universe.')
 E+=p('Budgets were 1200seconds,18,000 generated-output admission ceiling,180 operations,96 responses,4CPU,64GiB RAM and12GiB scratch per session. Model alias gpt-6.2-sol/high via CLI 0.172 was offered live; no immutable provider revision or provider sampling seed was available. The order seed does not make future model outputs deterministic.')
 E+=card('Primary outcomes stay frozen',p('Three sessions were admissible: two B_named and one C_network. Thirteen stopped at the generated-output admission ceiling. Those are censored primary outcomes, not mathematical failures or OOM events. A later proof check does not retroactively make them primary successes.'),'pending')
 rows=[]
 for row in data['exposure']:
  rows.append([esc(row['id']),esc(row['primary_status']),esc(row['verification_status']),esc(row['mathematical_conclusion']),esc(row['premise_limit'])])
 E+=table(['Locked session','Original primary status','Separate proof replay','Exact mathematical contribution','Premise / endpoint limit'],rows)
 E+=p('All 13 censored payloads were checked separately under the same richest original D runtime, offline and with no new inference. Two exported drafts differed from their LOCK hashes. Exact bytes were recovered from the original timely snapshots/write traces; three missing or mismatched narratives were also recovered by exact hash. The later stronger draft was not substituted for the locked weaker one. Recovery scripts, exact provenance and failed harness attempts are retained.')
 E+=p('The strongest shared-premise results include attained rounded fixed-width3/5 densities; raw witness refinements below their exact supremum caps; and a genuine uniform growing-rank theorem. A fixed-parameter eventual statement cannot simply be evaluated at a rank that varies with the prime index: the accepted adaptive proof supplies uniform headroom. Extra Brun–Titchmarsh “shaving” inputs and uninstantiated flat-arm margin interfaces are reported explicitly.')
 E+=m(r'a_3=\frac{685251}{387796},\quad a_5=\frac{465}{128};\qquad R_3=\frac{193269011844967139}{109374342622661960},\quad R_5=\frac{31036198331144443607}{8533333333333333328}',True)
 E+=p('The new B_named fixed-width improvement is proved for all widths at least1.03. Its comparison with the old explicit theorem is restricted to the old domain '+m(r'1.03\le c\le16')+'; it does not extend that theorem’s explicit-onset guarantee.')
 E+=p('The rounded endpoints are attained. Stronger raw GoodCoefficient claims are proved only for '+m(r'\alpha<R_3')+' or '+m(r'\alpha<R_5')+', or in limiting-margin forms—not as membership at the raw cap. Conditional transfer lemmas, closed RH consumers and written specializations are different result tiers. With only four sessions per arm and heavy primary censoring, these data establish no overall PV/network superiority. Compilation counts are not the primary strength metric.')
 sections.append(('exposure','Controlled exposure: all 16 outcomes',E))
 F=p('The following audit covers exactly the named mathematical inputs selected for the final theorem routes, using current written declaration identity, not a nearby-citation heuristic or old sorry queue. Source-family names are provenance candidates. Each row retains the actual declaration, canonical Blueprint correspondence and primary locator. This is not an audit of unrelated IEANTN source claims.')
 for row in data['source_audit']:
  lean=row['lean'];primary=row['primary'];bp=row.get('canonical_blueprint')
  formula=primary.get('formula_tex','');formula=formula.replace('\\\\','\\')
  body=p('Lean: '+source(lean['file'],lean['declaration'],lean['line']))
  if bp:body+=p('Blueprint correspondence: '+source(bp['file'],bp['declaration'],bp['line'])+'. '+esc(row.get('blueprint_note','')))
  body+=p('Primary: '+link(primary['locator'],primary['url'])+'.')
  if formula:body+=m(formula,True)
  body+=p('Source domain: '+esc(primary['domain']))
  body+=p(esc(row['comparison'])if isinstance(row['comparison'],str)else esc(row['comparison'].get('explanation',row['comparison'].get('conclusion','See the exact machine-readable comparison ledger.'))))
  body+=p('The published analytic or historical proof remains an explicit mathematical hypothesis.'if row.get('remains_explicit_mathematical_hypothesis')else'This component is proved in the supplied Lean development.')
  F+=details(esc(row['id'])+' — exact source and formal contract',body)
 F+=p('No material source-to-contract mismatch was found in the audited input families. The previously broader zero-transfer scheme was a real additional proof obligation and is now discharged. Historical direct computations remain literature-backed. Metadata fingerprints and local canonical checks are not official Comparator approval receipts.')
 sections.append(('sources','Sources, hypotheses and audit scope',F))
 G=p('Canonical evolution adds proved zero-summation and source-linked Fourier-norm providers while preserving old nodes and the original prime statements. A theorem consumer receives propositions through named dependencies; a new provider must prove precisely those propositions. Exact interface bridges and separate Solution builds check this correspondence. The changed source norm and newly proved zero transfer are actually traversed in the final proof-value audit.')
 G+=p('Generated Challenge files deliberately contain permanent statement-template sorry stubs. They are compiled in separate environments for interface checking; accepted Solution proof closures never consume those stubs. Accepted closures are audited to contain only '+m(r'\operatorname{propext},\ \operatorname{Classical.choice},\ \operatorname{Quot.sound}')+'. New numerical outputs are never installed as axioms or desired-result premises.')
 sections.append(('network','How IEANTN propagates the result',G))
 H=p('Source-cold means every selected application dependency was rebuilt from source with only the pinned generic libraries available. Source-associated means selected new modules were compiled over dependency objects whose exact source/snapshot/compiler-receipt/object identities were validated. The two must not be conflated.')
 H+=table(['Run','Fresh / associated sources','Elapsed','Measured memory','Disk / OOM / limits'],[[esc(r[k])for k in ['id','compilation','time','memory','limits']]for r in data['resources']])
 H+=p('Resource admission checked RAM and disk separately. Runs could use up to 300 GiB memory when at least 1 TiB RAM was actually available; scratch had its independent 300 GiB cap and a 290 GiB stop reserve. Host reserve, process limits and live telemetry were recorded. Sampled group RSS is a lower bound on aggregate peak, not an exact high-water mark.')
 H+=p('Duplicate immutable compilation objects were hash-checked and shared without losing paths or bytes. Final cleanup removes only verified-regenerable experiment-owned temporary material after reproduction checks. Original sources, locked inputs, accepted artifacts and irreplaceable evidence remain. '+esc(data['cleanup_summary']))
 H+=details('Reproduce from a clean environment','<pre>'+esc(data['reproduce_commands'])+'</pre>'+p('Pin Lean4.34.0-rc2, Mathlib71a80585ee495fc24472fd0eaffc89d94e4fd8d6 and all eight generic dependencies recorded in the bundle. Numerical inputs, random/order seeds, source hashes, exact commands, actual stdout, proof receipts and artifact SHA256 values are preserved. Clean verification is deterministic; rerunning model-driven research need not reproduce provider outputs.'))
 H+=p('The evidence bundle manifest lists every member and SHA256. Large prime lists, redundant arrays and caches are regenerated by scripts where applicable; no missing artifact is concealed behind a receipt. Interrupted, diagnostic-failing, source-mismatched or censored runs retain their original status.')
 sections.append(('reproduce','Reproduction, resources and cleanup',H))
 I=p('The study connects original source programs to conditional prime theorems through independently specified syntax, actual modeled execution, exact arithmetic and analytic transfer. Its main advance is the closed proof chain and reuse of stronger numerical information; source verification alone does not improve an already established coefficient. The new Gaussian and population witnesses give separate mathematical improvements. The full-class dual obstruction explains why the fixed CMS functional cannot reach0.8.')
 I+=p('Negative results matter: no proved sub0.8 eventual reduction; no optimality theorem; stronger dual numerical proposals remain outside Lean; finite and eventual onsets cannot be exchanged; sparse controlled trials establish no general exposure advantage. The finite historical computation, named literature inputs and precise platform contracts remain visible assumptions.')
 sections.append(('exposition','Research exposition and limitations',I))
 K='<div lang="ko">'+p('이 연구는 RH를 가정한 소수 간격·소수 개수 정리와 실제 C 프로그램의 검증을 연결합니다. RH 자체를 증명한 것은 아닙니다. 논문에서 가져온 해석적 명제와 과거 유한 계산은 이름을 붙인 가정으로 남겨 두었습니다.')
 K+=p('새로운 핵심은 실제 소스, 독립적인 구문 관계, 실행 의미론, 정수 계산, 적분 경계, 최종 소수 정리를 한 증명 경로로 연결한 것입니다. 일반화된 영점 부분합 공식은 별도 가정에서 Lean 정리로 바뀌었습니다. 프로그램 검증만으로 이미 알려진 계수가 자동으로 좋아진다는 주장은 하지 않습니다.')
 K+=p('점근적 가우스 계수는 '+m(q+r'<0.833945313')+'이며 구체적인 시작점은 없습니다. 유한 구간의0.8,0.74,0.75와 전체 구간의0.851062는 보고서 표에 적힌 실제 검증 상태·범위·가정을 따라 읽어야 합니다. 수치로 확인한 더 강한 쌍대 경계와 Lean으로 증명한 경계도 구별했습니다.')
 K+=p('노출 실험16개의 원래 판정은 보존했습니다. 제한에 걸린13개를 나중에 검증했다고 원래 성공으로 바꾸지 않았습니다. 각 실험의 수학적 결과와 추가 가정을 따로 비교하며, 이 작은 표본으로 네트워크나 PV의 전반적 우월성을 주장하지 않습니다.')+'</div>'
 sections.append(('korean','한국어 수학 요약',K))
 font=base64.b64encode(a.font.read_bytes()).decode();font_hash=hashlib.sha256(a.font.read_bytes()).hexdigest()
 css='''@font-face{font-family:ReportMath;src:url(data:font/ttf;base64,FONTDATA) format('truetype')}*{box-sizing:border-box}html{scroll-behavior:smooth}body{margin:0;background:#f4f6fa;color:#172434;font:16px/1.65 system-ui,sans-serif}header{background:#102b46;color:#fff;padding:2.4rem max(5vw,1rem)}header>p{max-width:75ch;color:#dceaf7}header a{color:#bfe2ff}h1{font-size:clamp(1.65rem,4vw,2.8rem);line-height:1.16;max-width:27ch}main{max-width:1120px;margin:auto;padding:1rem}nav{display:flex;gap:1rem;flex-wrap:wrap;padding:1rem;background:#fff;border-bottom:2px solid #d7e0ea}nav a{font-size:.9rem}a{color:#075a9f;text-decoration:underline;text-underline-offset:3px}a:focus-visible,summary:focus-visible,.table-scroll:focus-visible{outline:3px solid #ce6500;outline-offset:4px}section{background:#fff;padding:1.6rem;margin:1.2rem 0;border:1px solid #dce3eb;border-radius:12px;scroll-margin-top:1rem}h2{font-size:1.55rem;color:#153b60;border-bottom:2px solid #dce8f3;padding-bottom:.5rem}h3{font-size:1.08rem;margin:.2rem 0}.card{color:#172434;border-left:5px solid #17826d;background:#edf8f4;padding:1rem;margin:1rem 0}.pending{border-color:#a36500;background:#fff5de}p{max-width:90ch}math{font-family:ReportMath,'STIX Two Math',serif;font-size:1.05em}.formula{max-width:100%;overflow:auto;padding:.6rem 0;break-inside:avoid}.formula math{font-size:1.12em}.table-scroll{max-width:100%;overflow:auto;margin:1rem 0}table{width:100%;border-collapse:collapse;font-size:.89rem}th,td{text-align:left;vertical-align:top;padding:.7rem;border:1px solid #d7e1eb;min-width:130px}th{background:#eaf1f8}td{overflow-wrap:anywhere}details{border:1px solid #cbd9e6;border-radius:6px;padding:.8rem;margin:.7rem 0}summary{cursor:pointer;font-weight:650;color:#164970}details[open] summary{margin-bottom:.7rem}pre{max-width:100%;overflow:auto;padding:1rem;background:#eef2f7;font-size:.82rem;line-height:1.6}figure{margin:1rem 0}.scientific-figure{max-width:100%;overflow:auto}.scientific-figure svg{min-width:640px;max-width:100%;height:auto}figcaption{font-size:.86rem;color:#435363}footer{overflow-wrap:anywhere;padding:1rem;color:#435363;font-size:.85rem}@media(max-width:600px){main{padding:.45rem}section{padding:1rem;margin:.7rem 0}header{padding:1.5rem 1rem}body{font-size:15px}h2{font-size:1.3rem}nav{gap:.6rem}}@media print{body{background:white}section{border:none;break-before:auto}nav{display:none}details{break-inside:avoid}.table-scroll,.formula{overflow:visible}table{font-size:8pt}header{background:white;color:black}header p{color:black}}'''.replace('FONTDATA',font)
 nav='<nav aria-label="Report contents">'+''.join('<a href="#'+sid+'">'+esc(title)+'</a>'for sid,title,_ in sections)+'</nav>'
 content=''.join('<section id="'+sid+'"><h2>'+esc(title)+'</h2>'+body+'</section>'for sid,title,body in sections)
 output='<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>RH: primal, dual and source-verified explicit intervals</title><style>'+css+'</style><header><p>IEANTN · conditional analytic number theory · '+esc(data['date'])+'</p><h1>RH: primal, dual and source-verified explicit intervals</h1>'+intro+'</header>'+nav+'<main>'+content+'<footer>Offline MathML · embedded STIX font SHA256 '+font_hash+' · data SHA256 '+hashlib.sha256(a.data.read_bytes()).hexdigest()+' · no external scripts, fonts or network needed.</footer></main></html>'
 if '\\('in output or '\\['in output or '$$'in output:raise ValueError('Raw TeX delimiter escaped the renderer')
 a.out.parent.mkdir(parents=True,exist_ok=True);fd,name=tempfile.mkstemp(prefix='.report-',dir=a.out.parent)
 try:
  with os.fdopen(fd,'w',encoding='utf-8')as f:f.write(output);f.flush();os.fsync(f.fileno())
  os.link(name,a.out)
 finally:os.unlink(name)
 print(json.dumps({'status':'RENDERED_COMPLETE'if complete else'RENDERED_EXPLICIT_DRAFT','bytes':len(output.encode()),'math_elements':output.count('<math '),'sha256':hashlib.sha256(output.encode()).hexdigest()}))
if __name__=='__main__':main()
