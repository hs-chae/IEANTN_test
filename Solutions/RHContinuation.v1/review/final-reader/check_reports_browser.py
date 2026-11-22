#!/usr/bin/env python3
"""Offline browser acceptance of frozen bilingual report bytes, with explicit errors."""
from pathlib import Path
import argparse,hashlib,importlib.metadata,json,os,sys,tempfile,time
from urllib.parse import unquote,urlparse
from playwright.sync_api import sync_playwright

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
 if not ok:raise ValueError(message)
def strict_json(path):
 def unique(pairs):
  d={}
  for k,v in pairs:
   if k in d:raise ValueError('duplicate key: '+k)
   d[k]=v
  return d
 return json.loads(path.read_text(),object_pairs_hook=unique,parse_constant=lambda x:(_ for _ in ()).throw(ValueError('nonfinite '+x)))
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False)
 ap.add_argument('--inputs',type=Path,required=True)
 ap.add_argument('--out',type=Path,required=True)
 a=ap.parse_args();inputs=strict_json(a.inputs);out=a.out.resolve()
 require(set(inputs)=={'reports','support'},'unexpected input fields')
 require(not out.exists(),'output directory must be fresh')
 for row in inputs['reports']+inputs['support']:
  require(set(row)=={'path','sha256'},'unexpected input row')
  require(digest(Path(row['path']))==row['sha256'],'frozen input changed: '+row['path'])
 out.mkdir(parents=True);records=[];network=[];started=time.monotonic()
 with sync_playwright() as p:
  browser=p.chromium.launch(headless=True);version=browser.version;executable=p.chromium.executable_path
  for row in inputs['reports']:
   f=Path(row['path']);lang='EN'if f.name.endswith('_EN.html')else'KO'
   for name,width in [('desktop',1280),('mobile390',390)]:
    context=browser.new_context(viewport={'width':width,'height':900},offline=True)
    context.route('http://**/*',lambda r:r.abort());context.route('https://**/*',lambda r:r.abort())
    context.on('request',lambda req:network.append(req.url)if req.url.startswith(('http://','https://'))else None)
    page=context.new_page();errors=[];page.on('pageerror',lambda e:errors.append(str(e)))
    page.goto(f.as_uri());page.evaluate('document.fonts.ready')
    state=page.evaluate('''()=>({width:innerWidth,documentWidth:document.documentElement.scrollWidth,math:document.querySelectorAll('math').length,font:document.fonts.check('16px STIX'),scripts:document.scripts.length,minMathHeight:Math.min(...[...document.querySelectorAll('math')].map(e=>e.getBoundingClientRect().height)),mapBranches:document.querySelectorAll('.map-lane').length,mapWidths:[...document.querySelectorAll('.map-lane')].map(e=>({left:e.getBoundingClientRect().left,right:e.getBoundingClientRect().right,width:e.getBoundingClientRect().width})),hasOfflineNote:document.body.innerText.includes('directory structure intact')||document.body.innerText.includes('폴더 구조를 유지'),hasSeven:document.body.innerText.includes('seven kernel-checked derived conclusions')||document.body.innerText.includes('파생 결론 7개'),hasBPTTitle:document.body.innerText.includes('The mean square of the error term in the prime number theorem')})''')
    require(state['documentWidth']==width,('whole-page overflow',lang,name,state))
    require(state['math']==63 and state['minMathHeight']>0 and state['font'],('static math/font',lang,name,state))
    require(state['scripts']==0 and not errors,('script/pageerror',lang,name,errors))
    require(state['mapBranches']==7 and all(x['left']>=0 and x['right']<=width for x in state['mapWidths']),('network-map fit',lang,name,state))
    require(state['hasOfflineNote']and state['hasSeven']and state['hasBPTTitle'],('required report text',state))
    hrefs=page.locator('a').evaluate_all('(els)=>els.map(e=>e.href)');local=[];fragments=[]
    for href in hrefs:
     u=urlparse(href)
     if u.scheme=='file':
      target=Path(unquote(u.path));require(target.is_file(),('missing relative link',href));local.append(href)
      if target==f and u.fragment:
       require(page.locator('[id="'+u.fragment+'"]').count()==1,('missing anchor',href));fragments.append(href)
    require(len(local)>20 and len(fragments)>=10,('link coverage unexpectedly small',len(local),len(fragments)))
    # Real keyboard link activation, followed by a local proof-source navigation.
    nav=page.locator('nav a[href="#network"]');nav.focus()
    require(nav.evaluate('(e)=>getComputedStyle(e).outlineStyle')!='none','missing visible keyboard focus')
    page.keyboard.press('Enter');page.wait_for_function('location.hash=="#network"')
    require(page.locator('#network').is_visible(),'network keyboard navigation')
    page.locator('.network-map').screenshot(path=str(out/(lang+'-'+name+'-network.png')))
    gm=page.locator('.map-lane a').filter(has_text='RHPrimeCounting.v1');gm.click()
    require('namespace RHPrimeCounting.v1'in page.locator('body').inner_text(),'actual local statement link did not open source')
    page.goto(f.as_uri());page.evaluate('document.fonts.ready')
    disclosure=[]
    for index,summary in enumerate(page.locator('details > summary').all()):
     summary.focus();page.keyboard.press('Enter')
     require(summary.evaluate('(e)=>e.parentElement.open'),('keyboard disclosure open',index))
     page.keyboard.press('Space')
     require(not summary.evaluate('(e)=>e.parentElement.open'),('keyboard disclosure close',index))
     disclosure.append(index)
    require(len(disclosure)>=2,'disclosure routes missing')
    page.locator('details.audit > summary').focus();page.keyboard.press('Enter')
    page.locator('details.audit > summary').scroll_into_view_if_needed()
    page.screenshot(path=str(out/(lang+'-'+name+'-source-checks.png')))
    # Browser-native scrolling of focusable overflowing regions must work.
    scrolls=[]
    for selector in ['.table','.formula']:
     checked=0
     for index,region in enumerate(page.locator(selector).all()):
      if not region.evaluate('(e)=>e.scrollWidth>e.clientWidth+2'):continue
      region.evaluate('(e)=>e.scrollLeft=0');region.focus();page.keyboard.press('ArrowRight')
      page.wait_for_function('(e)=>e.scrollLeft>0',arg=region.element_handle(),timeout=3000)
      amount=region.evaluate('(e)=>e.scrollLeft');require(amount>0,('keyboard horizontal scrolling',selector,index))
      scrolls.append({'selector':selector,'index':index,'scroll_pixels':amount});checked+=1
      region.evaluate('(e)=>{e.scrollLeft=0;e.blur()}')
      if selector=='.formula'and checked>=2:break
    if width==390:require(any(x['selector']=='.table'for x in scrolls)and any(x['selector']=='.formula'for x in scrolls),'mobile scrolling not exercised')
    page.evaluate('scrollTo(0,0)');page.screenshot(path=str(out/(lang+'-'+name+'-intro.png')))
    page.locator('#pnt').scroll_into_view_if_needed();page.screenshot(path=str(out/(lang+'-'+name+'-math.png')))
    state.update(language=lang,viewport=name,local_links_checked=len(local),fragment_links_checked=len(fragments),keyboard_disclosures=disclosure,keyboard_scrolls=scrolls,page_errors=errors)
    records.append(state);context.close()
  browser.close()
 require(not network,('unexpected external network requests',network))
 for row in inputs['reports']+inputs['support']:require(digest(Path(row['path']))==row['sha256'],'frozen input changed during browser run')
 artifacts=[{'path':p.name,'bytes':p.stat().st_size,'sha256':digest(p)}for p in sorted(out.glob('*.png'))]
 result={'status':'PASS_FROZEN_OFFLINE_EN_KO_DESKTOP_MOBILE390_KEYBOARD_DISCLOSURE_LINKS_AND_OVERFLOW','python':sys.version,'python_optimization':sys.flags.optimize,'playwright_version':importlib.metadata.version('playwright'),'chromium_version':version,'chromium_executable':executable,'chromium_sha256':digest(Path(executable)),'checker_sha256':digest(Path(__file__).resolve()),'inputs':inputs,'records':records,'external_network_requests':network,'screenshots':artifacts,'elapsed_seconds':time.monotonic()-started,'official_Comparator_receipt':False}
 fd,tmp=tempfile.mkstemp(prefix='.RESULT-',dir=out);os.close(fd);Path(tmp).write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');os.replace(tmp,out/'RESULT.json')
 print(json.dumps({'status':result['status'],'optimization':sys.flags.optimize,'screenshots':len(artifacts),'seconds':result['elapsed_seconds']}))
if __name__=='__main__':main()
