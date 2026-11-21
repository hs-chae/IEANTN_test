#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction
import datetime, hashlib, html, json, re, shutil

B=Path(__file__).resolve().parent
W=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-propagation-20261120')
F=W/'evaluator-private/final-locks/IEANTN_RH/files'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def locator(name,needle):
    lines=(F/name).read_bytes().split(b'\n'); hits=[i+1 for i,s in enumerate(lines)if needle.encode() in s]
    if len(hits)!=1:raise ValueError('ambiguous locator '+name+' '+needle)
    return {'file':str(F/name),'line':hits[0],'sha256':sha(F/name)}
component=json.loads((B/'fresh-components-v1/RESULT.json').read_text())
numerical=json.loads((B/'numerical-v2/RESULT.json').read_text())
if component['status']!='PASS_EXACT_FINAL_7_COMPONENTS_FRESH_STANDARD_AXIOMS':raise ValueError('components not accepted')
if numerical['status']!='PASS_IDENTICAL_FROZEN_OUTPUTS_NORMAL_O_OO_NO_PROOF_INFERRED':raise ValueError('numerical not accepted')
paper=Path('/data/ivy-rh-propagation-20261120/setup/evaluator-literature/buthe-analytic-v2.pdf')
gm=Path('/data/ivy-rh-propagation-20261120/literature/IEANTN_RH/admissions/gm-ideal/SOURCE.pdf')
johnston=Path('/data/ivy-rh-propagation-20261120/setup/evaluator-literature/johnston.pdf')
table=W/'network/IEANTN/Nodes/Buthe/v1/Tables.lean'
s=table.read_text().split('def table_1 :',1)[1].split('def table_2 :',1)[0]
rows=[(int(m or 1)*10**int(n),Fraction(a),Fraction(b))for m,n,a,b in re.findall(r'\((?:(\d+) \* )?10 \^ (\d+), (-?[0-9.]+), (-?[0-9.]+)\)',s)]
# Independent transcription from the actual primary PDF Table1, p14 image.
blocks=[(10,[-77,-75,-73,-80,-88,-88,-66],[85,64,80,86,68,78,74]),
        (12,[-80,-79,-73,-80,-80,-67,-78],[81,76,73,76,68,93,77]),
        (14,[-79,-60,-65,-81,-66,-74,-73],[72,76,73,88,86,86,66]),
        (16,[-88,-87,-65,-82,-71,-78,-94,-94,-82,-83],[74,70,73,77,92,71,82,75,86,94])]
primary=[(2**i*10**power,Fraction(a,100),Fraction(b,100))for power,aa,bb in blocks for i,(a,b)in enumerate(zip(aa,bb))]
if rows!=primary or len(rows)!=31:raise ValueError('source Table1 differs')
selected=['GapFromSource.lean','CoefficientPV.lean','rh_coeff.c','Ramanujan.md','refined_ram.py','ram_cert.py','johnston_tail.py','crossing_cert.py','RealCrossing.lean','CrossingBracket.lean','FullRH.lean','SharedRH.lean','RamAlgebra.lean','Weighted.md']
(B/'frozen-sources').mkdir(exist_ok=True)
for name in selected:shutil.copyfile(F/name,B/'frozen-sources'/name)
verdict={'schema':'FINAL_FULL_RAMANUJAN_BOUNDED_INDEPENDENT_REVIEW_V1',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'Final full-arm Ramanujan additions: actual C coefficient conditional consumer, real crossing bracket, written610b/Table1/GM route, and Johnston quantitative tail. No NL outputs read; no worker contacted; no retroactive discovery credit.',
 'verdict':'NO_CONCRETE_MATHEMATICAL_DEFECT_FOUND_IN_SCOPED_ADDITIONS; formal/source boundaries below remain explicit.',
 'full_portfolio_external_source_census_completed':False,
 'proof_status':[
  {'claim':'GapFromSource.full_machine_gap','locator':locator('GapFromSource.lean','theorem full_machine_gap'),
   'status':'Fresh compiled exact final source, standard3 axioms; actual C returned-value polynomial consumed.',
   'premises':['1<l','Explicit analytic polynomial-vs-li truncation bound htrunc','Actual normalized pi upper bound hc at l','Actual normalized pi lower bound hd at l-1'],
   'boundary':'Conditional consumer. It does not discharge these three analytic/signed-count premises for610b or640b. C-language applicability independently audited by Root.'},
  {'claim':'CrossingBracket.root_in_bracket','locator':locator('CrossingBracket.lean','theorem root_in_bracket'),
   'status':'Fresh compiled, standard3 axioms, actual old C source count/exponential chain inherited.',
   'statement':'Unique local zero in(38358837682.217926,38358837682.217927); positivity on[A,A+1] exactly above it.',
   'boundary':'Global last-real assembly still requires explicit finite prefix and analytic ray providers; no independent whole-prefix proof.'},
  {'claim':'RG>=.001 for all real x>=610000000000','locator':locator('Ramanujan.md','## Second, earlier ray'),
   'status':'Written derivation reviewed; exact rational output29nodes/4empty/11accepted reproduced normal/O/OO; minimum84070619434703685709441311849298333738307/50000000000000000000000000000000000000000000.',
   'boundary':'No whole-theorem Lean provider or Python-source soundness proof. Printed numerical run is not a proof.'},
  {'claim':'Unconditional normalized margin>.379 on[exp42,exp59] and>.974 on[exp59,exp103]',
   'locator':locator('Ramanujan.md','## Non-grid quantitative recovery'),
   'status':'Written height/slab logic and exact9 scalar checks reviewed; frozen output reproduced normal/O/OO.',
   'boundary':'Uses published finite-height verification and Johnston analytic theorems; no independent replay of their finite zero/count computations.'}],
 'primary_sources':[
  {'file':str(paper),'sha256':sha(paper),'url':'https://arxiv.org/pdf/1511.02032v2',
   'locators':['Table1 printed/PDFp14, all31 signed rows and full closed[v,2v] domains compared','Theorem2(1.5),(1.8),(1.9),(1.10),p2; Lemma2 partial-summation identity(6.13),p15'],
   'source_claim':'Table1 bounds(t-psi(t))/sqrt(t) on every closed row, with exactly the31 source constants; global|psi(t)-t|<=.94sqrt(t) for11<t<=10^19. The program uses only the safe closed subset[12,10^19].'},
  {'file':str(gm),'sha256':sha(gm),'url':'https://arxiv.org/pdf/1312.4465v5',
   'locators':['Eq(1.3a),p2','Theorem1.1 Q-specialization,p3','Lemma3.3,p9','Q constant r_Q=log(2pi),p19'],
   'source_claim':'Primitive B0(t)=-sum_rho t^(rho+1)/(rho(rho+1))-t log(2pi)+rprime-sum_k t^(1-2k)/(2k(2k-1)); RH bound|B0(t)|<=.0462t^(3/2)+1.838t for t>=3.'},
  {'file':str(johnston),'sha256':sha(johnston),'url':'https://arxiv.org/pdf/2109.02249v2',
   'locators':['Theorem3.2(3.6),p4; normalization note p2','Theorem4.1(4.4) and Table2,p9','Theorem5.1,p10: all real38358837683<=x<=exp103, unconditionally'],
   'source_claim':'Finite RH height T>0 and9.06sqrt(x/logx)/loglogx<=T give pi error sqrt(x)logx/(8pi),x>=2657. Table2(a,K) gives a sqrt(x)logx when Ksqrt(x/log^3x)<=T,x>=2; explicitly also standard unnormalized counts.'}],
 'checks':{'table1_exact_rows':31,'exact_final_fresh_compiler_modules':7,'numerical_programs':3,'actual_normal_O_OO_numerical_runs':9,
   'GM_integrated_signs':'Correct: negative zero bracket, real -log2pi and positive small trivial-zero derivative.',
   'GM_sum_interchange':'Written primitive-first integration gives uniform finite-interval domination by constant/|rho|^2; no numerical zero list needed.',
   '610_scalar_domain':'l>=27, shifted>=26; square z/2>=13, k3..5 z/k>=5; same closed-slab cover logic and RH tail.',
   'Johnston_slab_domains':'Both x and x/e satisfy same row height bound; squared height functions increase for used L>=41 or L>=58; check right endpoint, losses at left endpoint.'},
 'separate_accepted640_proof':'Post-lock kernel theorem in ../../post-lock-verification/Ramanujan640-v1; exact8 source contracts including li-series/derivative. Does not consume CoefficientPV; never label it source-firstPV.',
 'minimal_needed_formal_repairs':['To formalize610b, prove the GM weighted-J bridge and stronger p8/p1/p3-at5 barriers, plus eleven leaf scalar/continuous transport closure; the C coefficient component alone does not close those obligations.','To make the local zero global in Lean, supply actual finite Johnston prefix theorem and compiled all-real analytic ray rather than only written providers.'],
 'source_pins':{n:sha(F/n)for n in selected},
 'receipts':{'components':{'file':str(B/'fresh-components-v1/RESULT.json'),'sha256':sha(B/'fresh-components-v1/RESULT.json')},'numerical':{'file':str(B/'numerical-v2/RESULT.json'),'sha256':sha(B/'numerical-v2/RESULT.json')}}}
(B/'VERDICT.json').write_text(json.dumps(verdict,indent=2)+'\n')
E=html.escape
bp=W/'network/IEANTN/Nodes/RamanujanGap/v1/Conclusions.lean'
parts=['<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Final full-arm Ramanujan review</title><style>body{font:16px system-ui;max-width:1050px;margin:25px auto;padding:0 14px;color:#20313b;background:#f5f7fa}h1{font-size:26px}h2{font-size:20px}article{background:white;border-left:6px solid #368852;padding:15px 20px;margin:16px 0;border-radius:6px}.amber{border-color:#bf8a24}.math{font:20px Georgia;overflow-wrap:anywhere;background:#edf3f8;padding:12px;margin:9px 0}a{color:#175d99}code{font-size:13px;overflow-wrap:anywhere}small{color:#52636c}</style><h1>Final full-arm Ramanujan additions</h1><p><b>No concrete mathematical defect found in this bounded review.</b> Seven exact final Lean components compiled in a fresh output tree. The three frozen numerical programs reproduced identical output in normal, -O and -OO modes. Execution evidence is separate from proof.</p>']
parts.append('<p>No standalone Blueprint labels exist for these new arm declarations. Their actual inequality is the imported <a href="'+E(str(bp))+'">RamanujanGap Blueprint-facing module</a>. This is not a complete external-source census of the full portfolio.</p>')
parts.append('<article><h2>Actual C outputs reach a conditional gap theorem</h2><p><a href="frozen-sources/GapFromSource.lean">GapFromSource.full_machine_gap</a> uses the evaluated C return values in <code>machinePolynomial</code>, proves their equality to the mathematical degree20 polynomial, and passes that polynomial to the actual signed-count consumer.</p><div class="math">ℓ⁴P<sub>C</sub>(1/ℓ)−0.001 − ℓ⁵d/(ℓ−1) + ℓ⁴[2w(ℓ)c−c²] ≤ R<sub>G</sub>(e<sup>ℓ</sup>).</div><p>The analytic truncation inequality and the two actual signed count bounds are explicit premises. This is a valid conditional consumer, not a proof that those premises hold on the610-billion or640-billion rays. The separate640-billion kernel proof does not consume this C component. Exact C-language/source applicability is the parent’s separate audit.</p></article>')
parts.append('<article><h2>Actual local crossing: formally closed</h2><p><a href="frozen-sources/CrossingBracket.lean">CrossingBracket.root_in_bracket</a> consumes the inherited actual count and exponential executions, together with kernel atanh logarithm sums:</p><div class="math">38,358,837,682.217926 &lt; z &lt; 38,358,837,682.217927.</div><p>On the whole closed unit [38,358,837,682, 38,358,837,683], both prime counts are constant; the resulting gap is continuous and strictly increasing. Its sign is positive exactly above z. Johnston Theorem5.1, p10, states the unconditional all-real prefix38,358,837,683≤x≤exp103. Global formal extension still needs this finite prefix and the analytic ray providers explicitly present in <a href="frozen-sources/RealCrossing.lean">RealCrossing.last_real</a>.</p></article>')
parts.append('<article class="amber"><h2>The610-billion ray remains a written proof</h2><p><a href="frozen-sources/Ramanujan.md">Final Ramanujan.md, second ray</a> and <a href="frozen-sources/refined_ram.py">refined_ram.py</a> use <a href="https://arxiv.org/pdf/1511.02032v2#page=14">Büthe Table1, p14</a>, not Table2. All31 primary table rows, their signs and closed domains were independently compared. Theorem2(1.5), p2, states |ψ(t)−t|≤0.94√t for11&lt;t≤10<sup>19</sup>; the program’s global row uses the safe subset12≤t≤10<sup>19</sup>.</p><div class="math">m ≤ [t−ψ(t)]/√t ≤ M, &nbsp; v ≤ t ≤ 2v.</div><p><a href="https://arxiv.org/pdf/1312.4465v5#page=2">Grenié–Molteni Eq(1.3a), p2</a>, with <a href="https://arxiv.org/pdf/1312.4465v5#page=9">Lemma3.3, p9</a>, supplies the actual absolutely convergent primitive:</p><div class="math">B₀(t)=−Σ<sub>ρ</sub>t<sup>ρ+1</sup>/[ρ(ρ+1)]−t log(2π)+r′−Σ<sub>k≥1</sub>t<sup>1−2k</sup>/[2k(2k−1)].</div><p>Integrating before taking absolute values gives the stated transferred allowance. The extra terms are individually accounted for:</p><div class="math">Zero contribution ≤ 0.047(1+16/L)√x/L² + 0.047e⁴/64.</div><div class="math">Anchor ≤ 1.94e⁴/8; real and trivial terms ≤ 1.838/8.</div><div class="math">1.94e⁴/8 + 0.047e⁴/64 + 1.838/8 &lt; 14, &nbsp; 0.047(1+16/26)&lt;0.076.</div><div class="math">|J(x)−li(x)−[ψ(x)−x]/L| ≤14+0.076√x/L², &nbsp; L≥26.</div><p>The signs, constants, source domains and eleven-slab coverage were reviewed without finding a defect. The same frozen exact run has minimum0.0016814123886940736, above0.001. A full Lean proof of this weighted spectral bridge, stronger barriers and eleven-cell consumer is still absent.</p></article>')
parts.append('<article class="amber"><h2>Johnston quantitative tail: written, source-compatible</h2><p><a href="https://arxiv.org/pdf/2109.02249v2#page=4">Theorem3.2(3.6), p4</a> states the actual source formula:</p><div class="math">|π(x)−li(x)| &lt; √x log x/(8π), &nbsp; x≥2657, &nbsp; 9.06√[x/log x]/log log x ≤ T.</div><p><a href="https://arxiv.org/pdf/2109.02249v2#page=9">Theorem4.1(4.4), Table2, p9</a> instead states:</p><div class="math">|π(x)−li(x)| &lt; a√x log x, &nbsp; x≥2, &nbsp; K√[x/(log x)³] ≤ T.</div><p>The source explicitly permits standard right-continuous counts (p2). At T=3×10¹² the final program checks the nine complete slabs, both x and x/e remain admissible, and the transferred losses decrease within each fixed row. These establish the claimed written quantitative range using the published verification. They do not independently reproduce that verification or Johnston’s earlier prefix.</p></article>')
parts.append('<p><small>Exact primary hashes, declaration byte-LF locators, source pins, all seven fresh compiler logs, and nine exact numerical replay receipts are in VERDICT.json and the adjacent evidence directories. Frozen900s/1800s sources and discovery inputs were not edited.</small></p></html>')
(B/'REVIEW.html').write_text(''.join(parts));print(verdict['verdict'])
