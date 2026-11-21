from pathlib import Path
import sys,json,hashlib,base64,html,shutil
B=Path(__file__).resolve().parent
SUP=Path('/data/ivy-rh-propagation-20261120/post-lock-verification/MertensPositive-v1/render-support')
sys.path.insert(0,str(SUP));from latex2mathml.converter import convert
R=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-rh-propagation-20261120/evaluator-private/final-locks')
(B/'sources').mkdir(exist_ok=True)
for arm in ['NL_RH','IEANTN_RH']:shutil.copy2(R/arm/'files/Intervals.md',B/'sources'/f'{arm}-Intervals.md')
esc=html.escape
def eq(t):return '<div class="eq">'+convert(t,display='block')+'</div>'
def p(s):return '<p>'+s+'</p>'
font=base64.b64encode((SUP/'fonts/STIXGeneral.ttf').read_bytes()).decode()
css="""@font-face{font-family:STIX;src:url(data:font/ttf;base64,FONT)}*{box-sizing:border-box}body{margin:0;padding:18px;background:#edf2f6;color:#183047;font:16px/1.5 system-ui}main{max-width:1050px;margin:auto}header,article{background:white;border:1px solid #d5e0e8;border-left:6px solid #278361;border-radius:9px;padding:19px;margin:13px 0}h1{font-size:27px;line-height:1.2}h2{font-size:20px}.eq{overflow:auto;background:#f2f6fa;padding:11px;margin:10px 0;max-width:100%}math{font:20px STIX,serif}p{overflow-wrap:anywhere}a{color:#145e98}.note{border-left-color:#b18735}.meta{font-size:13px;color:#516b82}pre{white-space:pre-wrap;font-size:12px}@media(max-width:600px){body{padding:6px}header,article{padding:13px}math{font-size:18px}}""".replace('FONT',font)
out=['<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta http-equiv="Content-Security-Policy" content="default-src \'none\';style-src \'unsafe-inline\';font-src data:"><title>Independent review: effective forward2.43 corollary</title><style>'+css+'</style><main><header><p class="meta">Independent mathematical check · ROOT POST-LOCK COROLLARY · 20 November 2026</p><h1>The effective forward2.43 count holds on the entire ray</h1>',
eq(r'\mathrm{RH},\ u\ge e^{24}\quad\Longrightarrow\quad\#\{p\ {\rm prime}:u<p<u+2.43\sqrt u\log u\}>\left(1+\frac{.04}{\log u}\right)\sqrt u.'),
p('<strong>Verdict: valid from the reviewed NL parabolic core.</strong> This is a new post-lock parameter conversion and is not credited as an original NL-arm claim. No Lean proof or source-first program verification is claimed. Long equations scroll within their boxes.'),'</header>']
out+=['<article><h2>1 · Exact inherited core and status</h2>',p('The frozen <a href="sources/NL_RH-Intervals.md">NL Intervals.md, “Parabolic window: stronger explicit finite band”</a>, states under RH:'),
eq(r'L\ge24,\quad D_1=.465L-.93\log L-.25,\quad D_1\le D\le2L,\quad\delta=De^{-L/2},\quad a=e^{L-\delta},\ b=e^{L+\delta},'),
eq(r'\#\{p:a<p<b\}>\left[\frac43(D-D_1)+.04\right]\frac{\sqrt a}{\log a}.'),
p('Its validity was independently reviewed in <a href="../final-NL/REVIEW.html">the final NL review</a>. It is written RH analysis using the explicit zero-count formula, the integrated explicit formula, and directed trigonometric quadrature with continuous-variation and infinite-tail allowances. Those analytic inputs and the quadrature are inherited; this note does not upgrade them to a complete Lean proof or verified source execution. No new zero, Fourier, or numerical hypothesis is added.'),'</article>']
out+=['<article><h2>2 · Every requested lower endpoint is reached</h2>',
eq(r'D=D_1+\frac34L=\frac{243}{200}L-\frac{93}{100}\log L-\frac14.'),
p('For all L≥24, D≥L and D&lt;1.215L&lt;2L. Indeed log24&lt;3.2 gives D(24)&gt;25.934&gt;24, while the derivative of D−L is .215−.93/L&gt;0. The logarithm bound follows from exp(3.2)&gt;2.7³(1+.2+.2²/2)&gt;24.'),
eq(r'0<\delta<1.215\cdot24e^{-12}<1.215\cdot24(10/27)^{12}<\frac1{5000},\qquad \delta^{\prime}=e^{-L/2}(D^{\prime}-D/2)<0.'),
p('The bound uses that L exp(−L/2) decreases from24 and exp(1)&gt;2.7. For the derivative, D′≤1.215 and D≥L imply D′−D/2≤1.215−L/2&lt;0.'),
p('Given any u≥exp24, put ℓ=log u≥24 and f(L)=L−δ(L). This continuous function has derivative greater than1. Moreover f(24)&lt;24≤ℓ, while f(ℓ+1)&gt;ℓ+1−1/5000&gt;ℓ. The intermediate value theorem therefore supplies a unique L in (24,ℓ+1) with f(L)=ℓ. Thus a=u, and every source-domain condition holds, including at u=exp24.'),'</article>']
out+=['<article><h2>3 · The whole open interval fits inside width2.43</h2>',
eq(r'\frac{b-a}{\sqrt a\log a}=\frac{2D}{L}\,e^{\delta/2}\frac{\sinh\delta}{\delta}\frac1{1-\delta/L}\le\frac{2D}{L}(1+\delta)^3\le\frac{2D}{L}(1+4\delta).'),
p('All three factors are at most1+δ. For the exponential, log(1+δ)≥δ/2 when0≤δ≤1. For the hyperbolic factor, sinhδ/δ≤coshδ≤1+δ²≤1+δ: the power series and cosh1&lt;2 give the middle bound. For the reciprocal factor the assertion is equivalent to L≥1+δ. Finally (1+δ)³≤1+4δ follows from3δ+δ²&lt;1. All apply on0&lt;δ&lt;1/5000. For completeness, the derivative of log(1+δ)−δ/2 is nonnegative for0≤δ≤1. Also sinhδ/δ≤coshδ by integrating cosh; the power series gives coshδ≤1+δ²(cosh1−1)&lt;1+δ². Here cosh1&lt;2 follows from exp1&lt;3 and exp(−1)&lt;1; exp1&lt;3 follows directly from n!≥2ⁿ⁻¹, strictly for n≥3.'),
eq(r'9.72L\delta<11.8098L^2e^{-L/2}\le11.8098\cdot24^2e^{-12}<11.8098\cdot24^2(10/27)^{12}<.05.'),
p('Here L²exp(−L/2) decreases for L≥24. The last exact rational upper bound is approximately .045322; it is strictly below .05.'),
eq(r'\frac{b-a}{\sqrt a\log a}<2.43-\frac{1.86\log L+.5}{L}+\frac{.05}{L}=2.43-\frac{1.86\log L+.45}{L}<2.43.'),
p('Consequently b&lt;u+2.43√u log u. The original open interval (a,b) is a subset of the claimed open forward interval. No endpoint atom or limiting prime-count correction is needed.'),'</article>']
out+=['<article><h2>4 · The strict count has the stated extra term</h2>',
eq(r'\#\{p:a<p<b\}>\frac{L+.04}{L-\delta}\sqrt a=\left(1+\frac{\delta+.04}{\log u}\right)\sqrt u>\left(1+\frac{.04}{\log u}\right)\sqrt u.'),
p('This proves the headline open-interval statement. The usual inclusive upper-endpoint quantity π(u+2.43√u log u)−π(u) is at least this open count, so it satisfies the same strict lower bound.'),'</article>']
out+=['<article class="note"><h2>Comparison and necessary qualifications</h2>',
p('The full-arm CMS adaptation in <a href="sources/IEANTN_RH-Intervals.md">the frozen IEANTN Intervals.md</a> proves the α=1 count with width2.64√u log u from <strong>u≥4·10¹⁸</strong>, not exp42. On that common domain the new2.43 theorem has a strictly narrower open window and a larger pointwise count guarantee; it also starts earlier, at exp24. This comparison concerns the α=1 branch, not every α in the full-arm family.'),
p('It does not improve CMS Theorem5’s narrower .88 existence-only window from u≥4. Nor does the decaying bonus alone prove liminf count/√u&gt;1 at the exact coefficient2.43: it proves a pointwise strict surplus and a limiting lower bound at least1. The separate original ε-enlargement argument still gives an infimum of strict-liminf coefficients at most2.43. No unknown optimal Fourier constant or global-priority claim follows.'),
p('Primary comparison: <a href="https://arxiv.org/pdf/1708.04122v2#page=5">CMS v2 Theorems3 and5, PDFpage5</a>, and its explicit §6 inequalities as used by the frozen full-arm derivation. The source premise is the reviewed parabolic core above, not a newly assumed desired forward bound.'),
p('Nine exact-rational finite constant checks passed in normal, −O and −OO modes. They support the displayed endpoint arithmetic; the derivatives, intermediate-value argument, inclusions and strict inequalities are proved in the text. Ordinary rational arithmetic checks are not kernel proofs or source-first PV.'),'</article>']
out+=['<footer><details><summary>Embedded STIX font license</summary><pre>'+esc((SUP/'fonts/LICENSE_STIX').read_text())+'</pre></details></footer></main></html>']
(B/'REVIEW.html').write_text(''.join(out))
pins=[]
for pth in [R/'NL_RH/files/Intervals.md',R/'IEANTN_RH/files/Intervals.md',Path('/data/ivy-rh-propagation-20261120/review/final-NL/REVIEW.json')]:pins.append({'path':str(pth),'sha256':hashlib.sha256(pth.read_bytes()).hexdigest()})
j={'status':'VALID_COMPLETE_ELEMENTARY_DERIVATION_FROM_REVIEWED_PARABOLIC_CORE','attribution':'ROOT_POST_LOCK_COROLLARY; not original NL-arm claim credit','statement':'For every realu>=exp24 underRH, open_count(u,u+2.43sqrtu logu)>(1+.04/logu)sqrtu; hence the same strict bound forpi difference.','domain_and_strictness':'All source parameters are admissible; everyu>=exp24 is reached by IVT; strict width inclusion and count preserve open endpoints.','core_status':'Reviewed written RH analysis with inherited source and directed-quadrature inputs; not newly formalized here.','comparison':'Dominates the full-arm alpha1 pointwise2.64 count onits exactdomainu>=4e18; not allalpha branches or CMSexistence.88.','liminf_qualification':'Decaying bonus alone doesnot establish strictliminf>1 at exact2.43; separateepsilon-enlargement givesinfimum<=2.43.','source_pins':pins,'nine_constant_checks':['CHECKS.json','CHECKS_O1.json','CHECKS_O2.json'],'new_Lean_proof':False,'source_first_PV':False,'discovery_workers_contacted':False,'source_or_locked_files_modified':False,'html_sha256':hashlib.sha256((B/'REVIEW.html').read_bytes()).hexdigest()}
(B/'REVIEW.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
