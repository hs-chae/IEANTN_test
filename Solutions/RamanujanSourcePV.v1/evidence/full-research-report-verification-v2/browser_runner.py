#!/usr/bin/env python3
from pathlib import Path
from playwright.sync_api import sync_playwright
import argparse,json,hashlib,importlib.metadata
p=argparse.ArgumentParser();p.add_argument('--report',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();f=a.report.resolve();out=a.out.resolve();out.mkdir(exist_ok=False);records=[];requests=[]
with sync_playwright() as p:
 b=p.chromium.launch(headless=True);version=b.version
 for name,width in [('mobile',390),('desktop',1280)]:
  page=b.new_page(viewport={'width':width,'height':900});page.bring_to_front();page.route('http://**/*',lambda route:route.abort());page.route('https://**/*',lambda route:route.abort());page.on('request',lambda req:requests.append(req.url)if req.url.startswith(('https://','http://'))else None);page.goto(f.as_uri());page.evaluate('document.fonts.ready');j=page.evaluate("""()=>({width:innerWidth,documentWidth:document.documentElement.scrollWidth,math:document.querySelectorAll('math').length,font:document.fonts.check('16px STIX'),scripts:document.scripts.length,mathHeights:[...document.querySelectorAll('math')].map(x=>x.getBoundingClientRect().height)})""")
  if j['documentWidth']!=width or j['math']!=70 or not j['font']or j['scripts']!=0 or min(j['mathHeights'])<=0:raise ValueError(j)
  j['keyboard_overflow_tables_checked']=[]
  for index,region in enumerate(page.locator('.scroll').filter(has=page.locator('table')).all()):
   if not region.evaluate('(e)=>e.scrollWidth>e.clientWidth+1'):continue
   region.evaluate('(e)=>e.scrollLeft=0');region.focus();page.keyboard.press('ArrowRight');page.wait_for_function('(e)=>e.scrollLeft>0',arg=region.element_handle(),timeout=3000);page.wait_for_timeout(200);pixels=region.evaluate('(e)=>e.scrollLeft')
   if pixels<=0:raise ValueError(('keyboard table scrolling',name,index))
   j['keyboard_overflow_tables_checked'].append(dict(index=index,scroll_pixels=pixels))
   region.evaluate('(e)=>{e.scrollLeft=0;e.blur()}')
  if name=='mobile'and not j['keyboard_overflow_tables_checked']:raise ValueError('mobile overflow test not exercised')
  if name=='mobile'and page.locator('.scroll-hint').first.evaluate('(e)=>getComputedStyle(e).display')=='none':raise ValueError('missing mobile scroll instruction')
  start=page.locator('h2').filter(has_text='13.').last.evaluate('(e)=>e.getBoundingClientRect().top+scrollY');end=page.locator('h2').filter(has_text='14.').last.evaluate('(e)=>e.getBoundingClientRect().top+scrollY')
  for i,y in enumerate(range(int(start),int(end)+1,850)):
   page.evaluate('(y)=>scrollTo(0,y)',y);page.screenshot(path=str(out/(name+'-13-'+str(i)+'.png')))
  records.append(dict(name=name,**j));page.close()
 b.close()
if requests:raise ValueError(requests)
j=dict(status='PASS_OFFLINE_MOBILE_DESKTOP_ALL70_MATH_EXPRESSIONS_AND_KEYBOARD_TABLE_SCROLL',report_bytes=f.stat().st_size,report_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),playwright_version=importlib.metadata.version('playwright'),chromium_version=version,records=records,external_network_requests=requests);(out/'RESULT.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({k:v for k,v in j.items()if k!='records'}))
