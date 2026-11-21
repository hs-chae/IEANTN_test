#!/usr/bin/env python3
"""Real offline desktop/mobile, links, MathML and keyboard disclosure checks."""
from pathlib import Path
from html.parser import HTMLParser
import hashlib,json
from playwright.sync_api import sync_playwright
R=Path(__file__).resolve().parents[1];S=R/'network/Solutions/RHExposureStudy.v1';P=S/'reports';O=R/'publication/report-browser-final';O.mkdir(exist_ok=True)
def need(b,s):
 if not b:raise ValueError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
class Links(HTMLParser):
 def __init__(self):super().__init__();self.paths=[]
 def handle_starttag(self,t,a):
  for k,v in a:
   if t=='a'and k=='href'and not v.startswith(('https:','http:','#')):self.paths.append(v)
rows=[]
with sync_playwright()as p:
 browser=p.chromium.launch(headless=True)
 for lang in ['EN','KO']:
  f=P/('RH_PROPAGATION_REPORT_'+lang+'.html');raw=f.read_text();need(not any(x in raw for x in ['\\frac','\\sqrt','\\(','$$']),'raw math markup');links=Links();links.feed(raw)
  for target in links.paths:need((f.parent/target).is_file(),'broken local artifact link:'+target)
  for view,w,h in [('desktop',1280,1000),('mobile',390,844)]:
   page=browser.new_page(viewport={'width':w,'height':h});requests=[];page.on('request',lambda r:requests.append(r.url));page.goto(f.as_uri(),wait_until='load');page.evaluate('document.fonts.ready')
   d=page.evaluate('''()=>({math:document.querySelectorAll('math').length,width:document.body.scrollWidth,viewport:innerWidth,font:document.fonts.check('20px STIX'),audit:document.querySelectorAll('details.audit').length,unexpectedTags:[...document.querySelectorAll('*')].filter(e=>e.tagName.includes('≤')).length})''')
   need(d['math']==117 and d['width']<=w+1 and d['font']and d['audit']==1 and d['unexpectedTags']==0,'initial document geometry/font:'+str(d));page.screenshot(path=str(O/(lang+'-'+view+'-top.png')))
   disclosure=page.locator('details.audit > summary');disclosure.focus();page.keyboard.press('Enter');need(page.locator('details.audit').get_attribute('open')is not None,'keyboard open');page.evaluate('document.fonts.ready');opened=page.evaluate('document.body.scrollWidth');need(opened<=w+1,'expanded audit overflow:'+str(opened));disclosure.scroll_into_view_if_needed();page.screenshot(path=str(O/(lang+'-'+view+'-audit.png')))
   disclosure.focus();page.keyboard.press('Enter');need(page.locator('details.audit').get_attribute('open')is None,'keyboard close')
   need(not any(u.startswith(('http:','https:'))for u in requests),'unexpected remote resource');rows.append({'lang':lang,'view':view,'html_sha256':sha(f),'dom':d,'expanded_width':opened,'local_links_checked':len(links.paths),'automatic_remote_requests':0,'keyboard_disclosure_open_close':True});page.close()
 version=browser.version;browser.close()
receipt={'status':'PASS_FINAL_EN_KO_OFFLINE_DESKTOP_MOBILE_LINKS_MATH_KEYBOARD','browser':version,'views':rows,'source_sha256':sha(__file__),'screenshots':[{'path':p.name,'sha256':sha(p)}for p in O.glob('*.png')]};(O/'RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'status':receipt['status'],'views':len(rows),'browser':version}))
