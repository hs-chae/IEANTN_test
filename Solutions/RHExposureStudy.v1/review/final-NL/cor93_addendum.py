#!/usr/bin/env python3
"""Additive post-lock CHCor9.3 comparison, independent of the manuscript reader pass."""
from pathlib import Path
import sys,json,hashlib,datetime
R=Path(__file__).parent;sys.path.insert(0,str(R/'replay'))
import bounds as b
F,I,PI,log,exp=b.F,b.I,b.PI,b.log,b.exp
checks={}
def check(k,x,relation,target):
 x=b.cast(x);q=b.cast(target);ok=x.gt(q) if relation=='>' else x.lt(q)
 if not ok:raise ValueError(k)
 checks[k]={'lower':str(x.l),'upper':str(x.h),'relation':relation,'target':str(q.l),'passed':True}
def B5(L):
 v=L/2-log(L);return (v*v+F('1.662')*v+F('1.148')+L)/(2*PI)+F('.14')
def C93(L):return ((L-2*log(L/(PI*exp(1))))**2-4)/(8*PI)
def A(L):
 u=L/2-log(L)+log(10/PI);return F('.158')*L+(u*u-u/3)/(2*PI)
L=F(35);v=L/2-log(L);h=1+log(PI);a=2*h-F('1.662');bb=h*h-F('2.148')
d=(a*v+bb-L)/(2*PI)-F('.14')
deriv=(a*(F(1,2)-1/L)-1)/(2*PI)
check('C93_minus_B5_at35',d,'>','.511')
check('C93_minus_B5_derivative_at35',deriv,'>','.037')
check('C93_positive_derivative_coefficient',a,'>',0)
T=2*PI**2*exp(L/2)/L
check('C93_source_T_condition_at35',T,'>',10**7)
check('Cor12_large_branch_x_above_T',exp(L)/T,'>',1)
check('Cor12_large_branch_x_above_1e9',exp(L),'>',10**9)
check('B5_at35_above_all_Table1_caps',B5(L),'>',40)
check('B5_coefficient_derivative_positive_at35',((2*v+F('1.662'))*(F(1,2)-1/L)+1)/(2*PI),'>',0)
check('full_A_above_C93_at34',A(F(34))-C93(F(34)),'>','.0037')
check('full_A_below_C93_at40',A(F(40))-C93(F(40)),'<','-.09')
rows=[('8e14','-.81','.88'),('1.6e15','-.66','.86'),('3.2e15','-.74','.86'),('6.4e15','-.73','.66'),('1e16','-.88','.74'),('2e16','-.87','.70'),('4e16','-.65','.73'),('8e16','-.82','.77'),('1.6e17','-.71','.92'),('3.2e17','-.78','.71'),('6.4e17','-.94','.82'),('1.28e18','-.94','.75'),('2.56e18','-.82','.86'),('5.12e18','-.83','.94')]
parsed=[]
for q,c,C in rows:
 s=F(q);lo=F(c);hi=F(C);cap=max(-lo,hi)
 if cap>F('.94') or lo>hi:raise ValueError('Invalid table row')
 parsed.append({'a':str(s),'b':str(2*s),'lower':str(lo),'upper':str(hi),'absolute_cap':str(cap)})
# Check no gap in the union of these actual closed Table1 intervals.
ordered=sorted(parsed,key=lambda z:F(z['a']));reach=F(ordered[0]['b'])
for row in ordered[1:]:
 if F(row['a'])>reach:raise ValueError('Table1 coverage gap')
 reach=max(reach,F(row['b']))
check('Table1_contains_e35_lower_endpoint',exp(35),'>',F(ordered[0]['a']))
if reach!=F('1.024e19'):raise ValueError('Unexpected finite upper endpoint')
source=R/'sources/chirre-helfgott.pdf';buthe=R/'sources/buthe.pdf'
obj={'schema':'FINAL_NL_CH_COR93_ADDITIVE_REVIEW_V1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'attribution':'post-lock independent reviewer source comparison; not discovery-arm credit','primary':{'paper':'Chirre–Helfgott, Optimal bounds for sums of non-negative arithmetic functions','version':'arXiv:2512.15709v1','locator':'Corollary9.3 equation9.4, PDFp36','url':'https://arxiv.org/pdf/2512.15709v1#page=36','pdf_sha256':hashlib.sha256(source.read_bytes()).hexdigest()},'source_domain_as_printed':'x>1, T=2*pi^2*sqrt(x)/log(x)>=1e7, RH throughT','audited_application_domain':'L=log(x)>=35; independently satisfies x>max(T,1e9), T>=1e7 and the large-x proof conditions','C93':'((L-2*log(L/(pi*e)))^2-4)/(8*pi)','verdict':'B5/sqrt(x)<C93-.5 for everyL>=35','uniform_proof':'difference derivative=(a*(1/2-1/L)-1)/(2*pi), a=2*(1+log(pi))-1.662; derivative increases and is positive at35; endpoint gap>.511','checks':checks,'finite_comparator':{'paper':'Büthe, An analytic method for bounding psi(x)','version':'arXiv:1511.02032v2','locator':'Table1 PDFp14; Theorem2 eq1.5 PDFp2','url':'https://arxiv.org/pdf/1511.02032v2#page=14','pdf_sha256':hashlib.sha256(buthe.read_bytes()).hexdigest(),'meaning':'lower<=(t-psi(t))/sqrt(t)<=upper on eachclosed[a,b]','rows':parsed,'frontier':'pointwise minimum of all applicable row absolute caps and global .94 on its original11<x<=1e19 domain','overlap':'exp35<=x<=1.024e19','comparison':'all finite table caps<=.94, while B5(L)>40 throughoutL>=35; finite published data dominate onoverlap'},'full_A_comparison':'A(34)>C93(34) by>.0037; A(40)<C93(40) by>.09. Retain pointwise minimum; B5 not admitted at34.','no_global_best_known_or_priority_claim':True,'new_full_Lean_proof':False,'source_first_PV':False,'optimization_mode':sys.flags.optimize}
name='ADDENDUM_CH_COR93'+('' if not sys.flags.optimize else '_O'+str(sys.flags.optimize))+'.json';tmp=R/(name+'.tmp')
tmp.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
tmp.replace(R/name)
if not sys.flags.optimize:
 table=''.join('<tr><td>'+q+'</td><td>'+c+'</td><td>'+C+'</td><td>'+str(max(-F(c),F(C)))+'</td></tr>' for q,c,C in rows)
 html='''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Addendum · CH Corollary9.3 and finite minima</title><style>body{max-width:980px;margin:24px auto;padding:20px;background:#f3f6fa;color:#193047;font:16px/1.6 system-ui}article{background:white;border:1px solid #d5deea;border-left:6px solid #31896d;border-radius:10px;margin:18px 0;padding:20px}h1{font-size:1.8rem}h2{font-size:1.25rem}.eq{font:1.03em/1.85 Cambria,serif;background:#edf3f8;padding:14px;border-radius:6px}td,th{padding:8px;border-bottom:1px solid #d8e1eb;text-align:left}table{width:100%;border-collapse:collapse}a{color:#185ba0}small{color:#53677b}</style><h1>Additive final-NL source comparison</h1><p>This note adds CH Corollary9.3 and the exact finite Büthe rows to the final comparison. It leaves the original final review and the separate manuscript-only reader pass unchanged. The comparison is post-lock reviewer work, with no discovery-arm credit.</p><article><h2>Exact source and admitted comparison domain</h2><p><b>Project:</b> final PNT.md B₅ is asserted only for L=log x≥35. There is no supplied full analytic Lean theorem for that implication.</p><p><b>Primary statement:</b> <a href="https://arxiv.org/pdf/2512.15709v1#page=36">Chirre–Helfgott v1, Corollary9.3, equation(9.4), PDFp36</a>, uses T=2π²√x/logx≥10⁷ and RH throughT, and gives</p><div class="eq">|ψ(x)−x|≤√x C₉₃(L),<br>C₉₃(L)=[(L−2log(L/(πe)))²−4]/(8π).</div><p>The corollary prints x&gt;1 with the displayed T condition. This comparison is restricted to the large-x branch L≥35: T&gt;10⁷ and x&gt;max(T,10⁹) are independently checked there and continue to hold. Thus the source’s preceding Corollary1.2 and the proof of(9.4) apply throughout the actual project range. No small-x extension is used.</p><p><b>Whole-function comparison.</b> Put v=L/2−logL and h=1+logπ. Then</p><div class="eq">C₉₃−B₅/√x<br>=[(2h−1.662)v+h²−2.148−L]/(2π)−0.14.</div><p>Its derivative is [(2h−1.662)(½−1/L)−1]/(2π), which increases withL and is positive at35. The difference at35 exceeds0.511, giving</p><div class="eq">B₅(x)/√x &lt; C₉₃(L)−0.5 &nbsp; for everyL≥35.</div><p>This is an additional exact-source comparison. It supports the scoped B₅ improvement and does not turn it into a global best-known or optimality assertion.</p></article><article><h2>Keep the stronger finite source data on the overlap</h2><p><b>Primary statement:</b> <a href="https://arxiv.org/pdf/1511.02032v2#page=14">Büthe v2, Table1, PDFp14</a> gives the following signed bounds on each closed interval [a,2a]:</p><div class="eq">m⁻ ≤ (t−ψ(t))/√t ≤ m⁺.<br>Therefore |ψ(t)−t|/√t ≤ max(−m⁻,m⁺).</div><table><tr><th>a</th><th>m⁻</th><th>m⁺</th><th>Absolute cap</th></tr>'''+table+'''</table><p>These applicable closed rows cover [exp(35),1.024·10¹⁹]. Where rows overlap, use their minimum, rather than arbitrarily choosing one. The last row covers [5.12·10¹⁸,1.024·10¹⁹]; the global0.94 statement in Theorem2(1.5) has its own smaller upper endpoint10¹⁹ and must not be silently extended.</p><p>Every table cap above is at most0.94, while B₅(L)&gt;40 forL≥35. Thus the finite published information is far stronger on this overlap, and it must remain in the pointwise source frontier. This is the exact finite frontier from the reviewed source, not an exhaustive census of every later finite result.</p></article><article><h2>The supplied full-arm A function also needs the source minimum</h2><p>The root-provided post-lock function A(L)=0.158L+[(v+k)²−(v+k)/3]/(2π), k=log(10/π), is slightly aboveC₉₃ atL34, but below it atL40. Exact checks give</p><div class="eq">A(34)−C₉₃(34)&gt;0.0037,<br>A(40)−C₉₃(40)&lt;−0.09.</div><p>B₅ has no admitted claim atL34. Preserve the pointwise minimum of compatible source functions and domains; one favorable comparison cannot justify an ordering over the entire ray.</p><p><small>Exact rational checks pass in default,−O and−OO: <a href="ADDENDUM_CH_COR93.json">JSON evidence</a>. New full analytic Lean proof and source-first PV remain unestablished. The primaryPDF bytes are pinned in the evidence directory.</small></p></article></html>'''
 (R/'ADDENDUM_CH_COR93.html').write_text(html)
print(json.dumps({'checks':len(checks),'passed':True,'optimization':sys.flags.optimize,'output':name}))
