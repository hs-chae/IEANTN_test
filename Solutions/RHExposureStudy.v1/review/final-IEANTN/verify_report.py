#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,re,sys
from playwright.sync_api import sync_playwright
B=Path(__file__).resolve().parent;f=B/'REVIEW.html';s=f.read_text();o=B/('browser'+(''if sys.flags.optimize==0 else '-O'+str(sys.flags.optimize)));o.mkdir(exist_ok=True)
if any(x in s for x in ['\\frac','\\(','$$']):raise RuntimeError('unrendered TeX')
for href in re.findall(r'href="([^"]+)"',s):
 if href.startswith(('#','http')):continue
 if not (B/href.split('#')[0]).is_file():raise RuntimeError('missing link '+href)
result=[]
with sync_playwright()as pw:
 browser=pw.chromium.launch(headless=True)
 for label,w,h in [('desktop',1240,950),('mobile',390,844)]:
  page=browser.new_page(viewport={'width':w,'height':h},device_scale_factor=1)
  page.goto(f.as_uri(),wait_until='load');page.evaluate('document.fonts.ready')
  data=page.evaluate("""()=>({math:document.querySelectorAll('math').length,width:document.body.scrollWidth,viewport:innerWidth,font:document.fonts.check('20px STIX'),cards:document.querySelectorAll('article[id]').length,raw:Array.from(document.querySelectorAll('.eq')).filter(x=>x.textContent.includes('\\\\frac')).length})""")
  if data['width']>w or not data['font']or data['math']<60 or data['cards']!=17 or data['raw']!=0:raise RuntimeError(str(data))
  page.screenshot(path=str(o/(label+'-top.png')))
  for id in ['E01','E02','W02','I03']:
   page.locator('#'+id).screenshot(path=str(o/(label+'-'+id+'.png')))
  result.append(dict(view=label,**data));page.close()
 browser.close()
j={'status':'PASS_LOCAL_LINKS_STATIC_MATH_DESKTOP_MOBILE','html_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'optimization':sys.flags.optimize,'views':result}
(o/'OBSERVATION.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
