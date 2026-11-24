#!/usr/bin/env python3
"""Actual offline Chromium mobile/desktop font, math and source-link gates."""
from pathlib import Path
import json,hashlib
from playwright.sync_api import sync_playwright
H=Path(__file__).resolve().parent;dest=H/'evidence/browser';dest.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rows=[]
with sync_playwright() as p:
 b=p.chromium.launch(headless=True)
 for width in [390,1100]:
  page=b.new_page(viewport={'width':width,'height':1100});errs=[];page.on('pageerror',lambda e:errs.append(str(e)))
  page.goto((H/'DERIVATION.html').as_uri());page.evaluate('document.fonts.ready')
  q=page.evaluate('''() => ({font:document.fonts.check('20px ReportSTIX'), scripts:document.scripts.length, math:Array.from(document.querySelectorAll('.math')).map(x=>x.textContent), external:Array.from(document.querySelectorAll('[src],[href]')).filter(e=>/^(https?:)?\\/\\//.test(e.getAttribute('src')||e.getAttribute('href')||'')).length, links:Array.from(document.querySelectorAll('a')).map(x=>x.getAttribute('href')), overflow:document.documentElement.scrollWidth>window.innerWidth})''')
  if not q['font'] or q['scripts'] or q['external'] or errs or any('$'in x or '\\['in x or '\\('in x for x in q['math']):raise ValueError('browser/math gate')
  if not all((H/x).is_file()for x in q['links']):raise ValueError('missing actual report source link')
  f=dest/('derivation-'+str(width)+'.png');page.screenshot(path=str(f),full_page=True)
  rows.append({'width':width,'font_loaded':q['font'],'page_errors':errs,'external_resources':q['external'],'script_count':q['scripts'],'math_blocks':len(q['math']),'all_source_links_exist':True,'whole_page_overflow':q['overflow'],'screenshot':str(f.relative_to(H)),'sha256':sha(f)})
 b.close()
(H/'BROWSER_RECEIPT.json').write_text(json.dumps({'status':'PASS_ACTUAL_OFFLINE_BROWSER_STATIC_MATH','report_sha256':sha(H/'DERIVATION.html'),'verifier_sha256':sha(Path(__file__)),'rows':rows,'visual_review':'Separate screenshot readback required; DOM/font gates alone are not visual inspection.'},indent=2)+'\n');print(json.dumps(rows,indent=2))
