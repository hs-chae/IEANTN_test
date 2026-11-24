#!/usr/bin/env python3
"""Build the standalone static-math explanation from pinned local font assets."""
from pathlib import Path
import base64,html,hashlib,json
H=Path(__file__).resolve().parent
S=H.parents[1]
font=S/'reports/fonts/STIXGeneral.ttf';license=S/'reports/fonts/LICENSE.txt'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
style='''@font-face{font-family:ReportSTIX;src:url(data:font/ttf;base64,FONT) format("truetype")}body{margin:1.3rem auto;padding:0 1rem;max-width:920px;color:#18242e;background:#f6f8fa;font:17px/1.55 system-ui,sans-serif}h1{font-size:1.9rem;line-height:1.2}h2{font-size:1.2rem}.card{background:white;border:1px solid #d5dce4;border-left:5px solid #21654a;border-radius:8px;padding:1rem;margin:1rem 0}.math{font-family:ReportSTIX,serif;font-size:1.14rem;overflow-x:auto;line-height:1.7;padding:.7rem;background:#edf3f8;border-radius:6px}.scope{border-left-color:#ad6b0b}a{color:#1456a3}table{border-collapse:collapse;width:100%;font-size:.95rem}td,th{padding:.5rem;border:1px solid #cbd4df;text-align:left}pre{white-space:pre-wrap;overflow-wrap:anywhere;font-size:.8rem}sup,sub{line-height:0}small{color:#546473}'''.replace('FONT',base64.b64encode(font.read_bytes()).decode())
body='''<h1>Prime-square feedback improves the complete ordinary-prime bound</h1>
<p>The same four-input result supplies a sharper estimate for primes at √x. Feeding that estimate into the actual square term improves the full prime-counting function. It also gives this clean corollary for every real x ≥ e<sup>100</sup>:</p>
<div class="math">|π(x) − Li₂(x)| &lt; √x · [log(x)/(8π) − 21/50].</div>
<p>Li₂ is the logarithmic integral starting at 2. The onset is unchanged from the preceding 2/5 corollary. The complete function below is stronger; neither optimality nor a best-known result is claimed.</p>
<section class="card"><h2>The mathematical mechanism is asymmetric</h2>
<p>Write J for Riemann’s prime-power counting function and li for the principal-value logarithmic integral. Positive higher prime powers give π(y) ≤ J(y). The completed ψ and compensated-J estimates therefore give an upper bound for π without needing an ordinary-prime error estimate as a premise.</p>
<div class="math">s ≥ 35: &nbsp; π(e<sup>s</sup>) ≤ J(e<sup>s</sup>) ≤ J<sub>up</sub>(s),<br>J<sub>up</sub>(s) = li(e<sup>s</sup>) + e<sup>s/2</sup>B(s)/s + P(s).</div>
<p>The proof has no circular feedback assumption. The existing ψ bound and signed J compensation are the inputs to this step.</p>
<div class="math">s ≥ 50: &nbsp; li(e<sup>s</sup>) ≤ (21/20)e<sup>s</sup>/s,<br>e<sup>s/2</sup>B(s)/s + P(s) &lt; e<sup>s</sup>/(20s),<br>so &nbsp; J<sub>up</sub>(s) &lt; (11/10)e<sup>s</sup>/s.</div>
<p><a href="FeedbackPiUpper.lean">Actual all-real upper bounds and full J function</a></p></section>
<section class="card"><h2>The actual square term, with the finite higher-power tail</h2>
<p>The inherited prime-power identity isolates the square term exactly. Its height is the original floor height; the finite higher-power sum is retained before applying its established upper bound.</p>
<div class="math">h(x) = ⌊log(x)/log(2)⌋,<br>J(x) − π(x) = ½π(√x) + Σ<sub>j=0,…,h(x)−3</sub> π(x<sup>1/(j+3)</sup>)/(j+3),<br>J(x) − π(x) ≤ ½π(√x) + x<sup>1/3</sup> log h(x).</div>
<p>For L = log x ≥ 70, use the full bound π(√x) ≤ J<sub>up</sub>(L/2). Define</p>
<div class="math">T(L) = ½e<sup>L/4</sup> + e<sup>L/3</sup>log(L/log 2),<br>Q<sub>old</sub>(L) = 2 log(4)e<sup>L/2</sup>/L + T(L),<br>Q<sub>raw</sub>(L) = ½J<sub>up</sub>(L/2) + T(L),<br>Q<sub>eff</sub>(L) = Q<sub>old</sub>(L) for L &lt; 70,<br>Q<sub>eff</sub>(L) = min[Q<sub>old</sub>(L), Q<sub>raw</sub>(L)] for L ≥ 70.</div>
<p>The old positive term e<sup>L/4</sup>/2 is conservatively retained. The minimum preserves every point of the original L ≥ 35 ray and cannot make its bound worse. The full lower-scale logarithmic integral and error functions are retained in Q<sub>raw</sub>.</p>
<p><a href="FeedbackPrimePowers.lean">Actual remainder and floor-height proofs</a> · <a href="../../../RHLimit.v1/pi/PrimePowerRemainder.lean">Inherited exact prime-power identity</a></p></section>
<section class="card"><h2>The complete improved function</h2>
<div class="math">v(L) = L/2 − log L,<br>B(L) = [v(L)² + 2 log(2)v(L) + 1.41742 + L]/(2π) + 0.14,<br>P(L) = 4.632 + 0.047[1 + 4/(L−8)]e<sup>L/2</sup>/L²,<br>U<sub>new</sub>(L) = e<sup>L/2</sup>B(L)/L + P(L) + Q<sub>eff</sub>(L) + 2.</div>
<p>The constant 2 still pays the principal-value li to Li₂ offset. Under the same four explicit inputs, for every real L ≥ 35:</p>
<div class="math">|π(e<sup>L</sup>) − Li₂(e<sup>L</sup>)| ≤ U<sub>new</sub>(L) ≤ U<sub>old</sub>(L).</div>
<p>Above L = 70 the new function is exactly the minimum of the complete old function and its raw lower-scale-J counterpart. Both interval endpoints are covered by the ordinary-prime difference consumer.</p>
<p><a href="FeedbackPi.lean">Complete function, strict gain and interval consumer</a></p></section>
<section class="card"><h2>A strict whole-function gain and a clean consequence</h2>
<p>For L ≥ 100, the 11/10 estimate is available at L/2. Thus Q<sub>raw</sub> is smaller than its simplified counterpart, and the old leading square coefficient decreases by more than 1.67:</p>
<div class="math">2 log(4) − 11/10 &gt; 167/100,<br>U<sub>old</sub>(L) − U<sub>new</sub>(L) &gt; (167/100)e<sup>L/2</sup>/L.</div>
<p>This compares the entire mathematical bound with the same assumptions. It includes P, every retained prime-power tail and the li offset.</p>
<div class="math">U<sub>new</sub>(L) &lt; [B(L) + 1.13]e<sup>L/2</sup>/L.</div>
<p>To prove the convenient 21/50 form, use log L ≥ 4.6, log L ≤ L/2 and log 2 ≤ 0.7. With t = L/2 − 4.6:</p>
<div class="math">B(L)+1.13 ≤ [t² + 1.4t + 1.41742 + L]/(2π) + 1.27.</div>
<p>After multiplication by 8π, the desired strict gap is</p>
<div class="math">[11.6 − 3.36π]L − 64.54968 − 10.16π &gt; 0.</div>
<p>Since π ≤ 22/7, the slope is at least 1.04, while the constant is less than 96.49. At every L ≥ 100 the positive linear term is at least 104. This proves the full real ray, including its endpoint; no sampled grid replaces the domain proof.</p>
<p><a href="FeedbackCorollary.lean">Scalar proof and exact canonical four-source consumer</a></p></section>
<section class="card"><h2>What the constants mean</h2>
<table><tr><th>Comparison</th><th>Proved result</th></tr><tr><td>Clean 2/5 versus clean 21/50</td><td>The right side decreases by exactly √x/50.</td></tr><tr><td>Complete new function at x = e<sup>100</sup></td><td>U<sub>new</sub>(100) &lt; 3.5537e<sup>50</sup>.</td></tr><tr><td>Complete old function at the same point</td><td>U<sub>old</sub>(100) &lt; 3.5704e<sup>50</sup>.</td></tr></table>
<p>These upper bounds describe theorem right sides, not measurements of the actual prime-counting error. The rounded clean function is weaker than the complete new function.</p></section>
<section class="card scope"><h2>Exact assumptions and verification boundary</h2>
<p>The consumers take precisely RH, the general integrated Perron formula, the Nicolas inverse-square zero bound, and the BPT off-ordinate zero-count estimate. The full Box explicit formula, infinite zero estimate and both Mellin moments are inherited proved constructions. No GM, Büthe, new prime table, guessed numerical premise or changed source program is introduced.</p>
<p>These genuine published source inputs remain explicit B-tier predicates. This is not an RH-only formalization. All 39 written new theorems have completed ordinary Lean kernel builds with only propext, Classical.choice and Quot.sound. Ordinary kernel verification is not source-first PV. No C/C++/CUDA compiler or execution claim is made by this analytic extension.</p>
<p>Original sources, frozen results, C/AST/model code and captured experiments are unchanged. The evidence records development and source-fresh verification separately. This report does not claim optimality, global novelty or a best-known bound.</p>
<p><a href="SOURCE_FREEZE.json">Exact sources and all 39 written identities</a> · <a href="README.md">Reproduction and current acceptance status</a></p></section>
'''
page='<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>Prime-square feedback</title><style>'+style+'</style>'+body+'<details><summary>Embedded font license</summary><pre>'+html.escape(license.read_text())+'</pre></details></html>'
(H/'DERIVATION.html').write_text(page)
(H/'FONT_RECEIPT.json').write_text(json.dumps({'font_path':str(font),'font_sha256':sha(font),'font_bytes':font.stat().st_size,'license_path':str(license),'license_sha256':sha(license),'report_sha256':sha(H/'DERIVATION.html'),'rendering':'Static HTML math, Unicode glyphs and embedded STIX font; no script, CDN or external math renderer.'},indent=2)+'\n')
print(sha(H/'DERIVATION.html'))
