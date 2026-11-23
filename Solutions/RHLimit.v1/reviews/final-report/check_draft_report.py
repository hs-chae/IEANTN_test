#!/usr/bin/env python3
"""Offline snapshot browser review: actual desktop/mobile math, overflow and keyboard behavior."""
from pathlib import Path
import argparse,hashlib,importlib.metadata,json,os,sys,time
from playwright.sync_api import sync_playwright

def need(b,m):
 if not b:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--input',type=Path,required=True);p.add_argument('--sha256',required=True);p.add_argument('--math-count',type=int,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();f=a.input.resolve();out=a.out.resolve();need(sha(f)==a.sha256,'snapshot input identity');need(not out.exists(),'fresh output required');out.mkdir(parents=True);start=time.monotonic();rows=[];issues=[];network=[]
 with sync_playwright()as p:
  browser=p.chromium.launch(headless=True);version=browser.version;executable=p.chromium.executable_path
  for name,width in [('desktop',1280),('mobile390',390)]:
   context=browser.new_context(viewport={'width':width,'height':900},offline=True)
   context.route('http://**/*',lambda r:r.abort());context.route('https://**/*',lambda r:r.abort());context.on('request',lambda req:network.append(req.url)if req.url.startswith(('http://','https://'))else None)
   page=context.new_page();errors=[];page.on('pageerror',lambda e:errors.append(str(e)));page.goto(f.as_uri());page.evaluate('document.fonts.ready')
   state=page.evaluate('''()=>({width:innerWidth,documentWidth:document.documentElement.scrollWidth,bodyWidth:document.body.scrollWidth,math:document.querySelectorAll('math').length,font:document.fonts.check('16px STIX'),scripts:document.scripts.length,minMathHeight:Math.min(...[...document.querySelectorAll('math')].map(e=>e.getBoundingClientRect().height)),tables:[...document.querySelectorAll('table')].map((e,i)=>({index:i,left:e.getBoundingClientRect().left,right:e.getBoundingClientRect().right,width:e.getBoundingClientRect().width})),overflowElements:[...document.querySelectorAll('main,main *')].filter(e=>{let r=e.getBoundingClientRect();return r.left<-.5||r.right>innerWidth+.5}).slice(0,40).map(e=>({tag:e.tagName,class:e.className.baseVal??e.className,text:e.textContent.slice(0,90),left:e.getBoundingClientRect().left,right:e.getBoundingClientRect().right})),details:document.querySelectorAll('details').length,links:document.querySelectorAll('a').length,rawTex:document.body.innerText.includes('\\\\(')||document.body.innerText.includes('\\\\[')})''')
   state['SVG']=page.evaluate('''()=>[...document.querySelectorAll('svg')].map(e=>({width:e.getBoundingClientRect().width,height:e.getBoundingClientRect().height,role:e.getAttribute('role'),label:e.getAttribute('aria-label'),title:e.querySelector('title')?.textContent,clippedBy:(()=>{for(let a=e.parentElement;a;a=a.parentElement){if(['auto','scroll','hidden','clip'].includes(getComputedStyle(a).overflowX))return {tag:a.tagName,tabindex:a.getAttribute('tabindex'),width:a.getBoundingClientRect().width,overflow:getComputedStyle(a).overflowX};}return null;})()}))''')
   if len(state['SVG'])!=1 or state['SVG'][0]['width']<=0 or state['SVG'][0]['height']<=0:issues.append({'viewport':name,'issue':'missing rendered SVG figure'})
   for cond,msg in [(state['documentWidth']<=width,'whole-page horizontal overflow'),(state['math']==a.math_count and state['minMathHeight']>0 and state['font'],'static math/font'),(state['scripts']==0 and not errors,'script/page error'),(not state['rawTex'],'raw TeX delimiters')]:
    if not cond:issues.append({'viewport':name,'issue':msg})
   page.screenshot(path=str(out/(name+'-intro.png')));page.screenshot(path=str(out/(name+'-full.png')),full_page=True)
   for heading,label in [('4. Ramanujan','ramanujan'),('5. Close','octic'),('6. Actual','analytic'),('8. Verification','resources'),('9. Trust','trust')]:
    locator=page.locator('h2').filter(has_text=heading)
    if locator.count()!=1:issues.append({'viewport':name,'issue':'missing unique section:'+heading});continue
    locator.scroll_into_view_if_needed();page.screenshot(path=str(out/(name+'-'+label+'.png')))
   figure=page.locator('svg');figure.scroll_into_view_if_needed();page.screenshot(path=str(out/(name+'-figure.png')))
   page.evaluate('scrollTo(0,0)');page.keyboard.press('Tab');first_focus=page.evaluate('''()=>({tag:document.activeElement.tagName,text:document.activeElement.textContent.slice(0,120),outline:getComputedStyle(document.activeElement).outlineStyle})''')
   focus=first_focus
   for _ in range(100):
    if focus['tag']=='A':break
    page.keyboard.press('Tab');focus=page.evaluate('''()=>({tag:document.activeElement.tagName,text:document.activeElement.textContent.slice(0,120),outline:getComputedStyle(document.activeElement).outlineStyle})''')
   if focus['tag']!='A'or focus['outline']=='none':issues.append({'viewport':name,'issue':'keyboard link focus invisible or absent','state':focus})
   disclosures=[]
   for index,summary in enumerate(page.locator('details>summary').all()):
    if summary.evaluate('(e)=>e.parentElement.open'):summary.evaluate('(e)=>e.parentElement.open=false')
    summary.focus();page.keyboard.press('Enter');opened=summary.evaluate('(e)=>e.parentElement.open');page.keyboard.press('Space');closed=not summary.evaluate('(e)=>e.parentElement.open');disclosures.append({'index':index,'opened':opened,'closed':closed})
    if not opened or not closed:issues.append({'viewport':name,'issue':'keyboard disclosure failure','index':index})
    summary.focus();page.keyboard.press('Enter')
   scrolls=[]
   page.evaluate('''()=>{let i=0;for(const e of document.querySelectorAll('main *')){if(e.getClientRects().length>0&&e.scrollWidth>e.clientWidth+2&&['auto','scroll'].includes(getComputedStyle(e).overflowX))e.setAttribute('data-review-scroll-index',i++);}}''')
   for index,region in enumerate(page.locator('[data-review-scroll-index]').all()):
    if not region.evaluate('(e)=>e.scrollWidth>e.clientWidth+2'):continue
    region.evaluate('(e)=>e.scrollLeft=0');region.focus();focused=region.evaluate('(e)=>document.activeElement===e');page.keyboard.press('ArrowRight');page.wait_for_timeout(180);amount=region.evaluate('(e)=>e.scrollLeft');scrolls.append({'index':index,'focused':focused,'pixels':amount})
    if not focused or amount<=0:issues.append({'viewport':name,'issue':'overflowing reading region not keyboard-scrollable','index':index,'focused':focused,'pixels':amount})
    region.evaluate('(e)=>{e.scrollLeft=0;e.blur()}')
   for index,summary in enumerate(page.locator('details>summary').all()):
    if summary.evaluate('(e)=>e.parentElement.open'):summary.focus();page.keyboard.press('Space')
    if summary.evaluate('(e)=>e.parentElement.open'):issues.append({'viewport':name,'issue':'disclosure did not close after reading','index':index})
   state.update(viewport=name,page_errors=errors,keyboard_first_focus=first_focus,keyboard_link_focus=focus,keyboard_scrolls=scrolls,keyboard_disclosures=disclosures);rows.append(state);context.close()
  browser.close()
 need(sha(f)==a.sha256,'snapshot changed during browser review');need(not network,'unexpected external requests')
 receipt={'status':'DRAFT_BROWSER_ISSUES_FOUND'if issues else'PASS_DRAFT_OFFLINE_DESKTOP_390_MATH_KEYBOARD_REVIEW','input':str(f),'input_sha256':a.sha256,'checker_sha256':sha(__file__),'python_optimization':sys.flags.optimize,'playwright':importlib.metadata.version('playwright'),'chromium_version':version,'chromium_executable':executable,'chromium_sha256':sha(executable),'seconds':time.monotonic()-start,'rows':rows,'issues':issues,'external_requests':network,'screenshots':[{'path':p.name,'sha256':sha(p),'bytes':p.stat().st_size}for p in sorted(out.glob('*.png'))],'final_report_acceptance':False}
 q=out/'.RESULT.pending';q.write_text(json.dumps(receipt,indent=2)+'\n');os.replace(q,out/'RESULT.json');print(receipt['status']);print(json.dumps(issues));raise SystemExit(1 if issues else 0)
if __name__=='__main__':main()
