#!/usr/bin/env python3
from pathlib import Path
from playwright.sync_api import sync_playwright
import hashlib,json
B=Path(__file__).resolve().parent;f=B/'MERTENS_POSITIVE_PROOF.html';o=B/'browser';o.mkdir(exist_ok=True)
if any(x in f.read_text()for x in ['\\frac','\\sum','\\(','$$']):raise RuntimeError('unrendered TeX')
rows=[]
with sync_playwright()as p:
 browser=p.chromium.launch(headless=True)
 for name,w,h in [('desktop',1240,950),('mobile',390,844)]:
  page=browser.new_page(viewport={'width':w,'height':h},device_scale_factor=1);page.goto(f.as_uri(),wait_until='load');page.evaluate('document.fonts.ready');d=page.evaluate('''()=>({math:document.querySelectorAll('math').length,width:document.body.scrollWidth,viewport:innerWidth,font:document.fonts.check('20px STIX')})''')
  if d['width']>w or not d['font']or d['math']<35:raise RuntimeError(str(d))
  page.screenshot(path=str(o/(name+'-top.png')));page.locator('article.card').nth(4).screenshot(path=str(o/(name+'-abel.png')));page.locator('article.card').nth(5).screenshot(path=str(o/(name+'-margin.png')));rows.append(dict(view=name,**d));page.close()
 browser.close()
r={'status':'PASS_OFFLINE_DESKTOP_MOBILE_MATH','html_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'views':rows};(o/'OBSERVATION.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
