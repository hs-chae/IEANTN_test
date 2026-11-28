#!/usr/bin/env python3
"""Offline presentation/source-link checks, not mathematical proof acceptance."""
import argparse,hashlib,importlib.metadata,json,os,re,subprocess,tempfile
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import unquote,urlsplit

def need(ok,message):
    if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def publish(path,value):
    fd,name=tempfile.mkstemp(dir=path.parent,prefix='.receipt-')
    try:
        with os.fdopen(fd,'w') as f:
            json.dump(value,f,indent=2,ensure_ascii=False,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(name,path)
    finally:os.unlink(name)
def norm(s):return ' '.join(s.split())
class Prose(HTMLParser):
    def __init__(self):super().__init__(convert_charrefs=True);self.current=None;self.rows=[]
    def handle_starttag(self,tag,attrs):
        if tag=='p':need(self.current is None,'Nested source paragraph');self.current=[]
    def handle_data(self,data):
        if self.current is not None:self.current.append(data)
    def handle_endtag(self,tag):
        if tag=='p':need(self.current is not None,'Unmatched source paragraph');self.rows.append(norm(''.join(self.current)));self.current=None

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--report',type=Path,required=True);ap.add_argument('--data',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True);ap.add_argument('--repository',type=Path)
    ap.add_argument('--enforce-committed-links',action='store_true');a=ap.parse_args()
    need(a.report.is_file() and a.data.is_file(),'Reading artifacts absent');need(not a.out.exists(),'Fresh QA directory required')
    a.out.mkdir(parents=True);browser_tmp=a.out/'browser-tmp';browser_tmp.mkdir();os.environ['TMPDIR']=str(browser_tmp);frozen=a.out/'REPORT_INPUT.html';frozen.write_bytes(a.report.read_bytes())
    data=json.loads(a.data.read_text());parser=Prose();parser.feed(frozen.read_text());need(parser.current is None,'Unclosed source paragraph')
    if a.enforce_committed_links:need(data['completion']['complete'] is True and a.repository is not None,'Final committed-link check requires complete data and repository')
    from playwright.sync_api import sync_playwright
    rows=[];screens=[];link_rows=[]
    with sync_playwright() as p:
        browser=p.chromium.launch(headless=True,args=['--enable-automation'])
        session=browser.new_browser_cdp_session();actual_browser=Path(session.send('Browser.getBrowserCommandLine')['arguments'][0]);session.detach()
        need(actual_browser.is_file(),'Actual browser binary absent');browser_identity=dict(path=str(actual_browser),sha256=sha(actual_browser),version=browser.version)
        for label,size in [('desktop',dict(width=1280,height=900)),('mobile',dict(width=390,height=844))]:
            context=browser.new_context(viewport=size,is_mobile=label=='mobile',has_touch=label=='mobile',offline=True)
            page=context.new_page();requests=[];errors=[]
            page.on('request',lambda r:requests.append(r.url if not r.url.startswith('data:') else 'data:sha256:'+hashlib.sha256(r.url.encode()).hexdigest()))
            page.on('pageerror',lambda e:errors.append(str(e)))
            page.goto(frozen.as_uri(),wait_until='load');page.evaluate('document.fonts.ready')
            first=page.locator('#sources details').first;summary=first.locator(':scope > summary')
            need(summary.count()==1,'Ambiguous disclosure control');summary.focus();page.keyboard.press('Enter');need(first.get_attribute('open') is not None,'Keyboard disclosure failed')
            page.evaluate('document.querySelectorAll("details").forEach(x=>x.open=true)')
            page.locator('.formula').first.focus();need(page.locator('.formula').first.evaluate('e=>e===document.activeElement'),'Formula keyboard focus failed')
            dims=page.evaluate(r'''()=>({width:innerWidth,scroll:document.documentElement.scrollWidth,body:document.body.scrollWidth,math:document.querySelectorAll('math').length,canonical:document.querySelectorAll('.canonical-claim').length,details:document.querySelectorAll('details').length,open:document.querySelectorAll('details[open]').length,rawTex:/\\(?:frac|sqrt|operatorname|begin|left)\b/.test(document.body.innerText),scripts:document.scripts.length,errors:document.querySelectorAll('merror,parsererror').length,formulaTabStops:document.querySelectorAll('.formula[tabindex="0"]').length,fonts:[...document.fonts].map(x=>({family:x.family,status:x.status})),visibleMath:[...document.querySelectorAll('math')].every(x=>{let r=x.getBoundingClientRect();return r.width>0&&r.height>0})})''')
            need(dims['width']==size['width'] and dims['scroll']<=size['width']+1 and dims['body']<=size['width']+1,'Viewport overflow')
            need(dims['canonical']==29 and dims['details']==dims['open'] and dims['math']>=156,'Missing report statements')
            need(not dims['rawTex'] and not dims['scripts'] and not dims['errors'] and dims['visibleMath'],'Static math rendering failed')
            need(any(x['family']=='ReportMath' and x['status']=='loaded' for x in dims['fonts']),'Embedded offline math font did not load')
            need([norm(x) for x in page.locator('p').all_text_contents()]==parser.rows,'Browser repaired/lost source prose')
            need(not errors and not any(x.startswith(('http:','https:')) for x in requests),'Report fetched network content or raised error')
            urls=page.locator('a[href]').evaluate_all('(xs)=>xs.map(x=>x.href)')
            if not link_rows:
                prefix='https://github.com/hs-chae/IEANTN_test/blob/'
                for u in sorted(set(x for x in urls if x.startswith(prefix))):
                    tail=unquote(urlsplit(u).path.split('/blob/',1)[1]);need('/' in tail,'A revision link must use /commit/COMMIT; blob links require a file');commit,rel=tail.split('/',1)
                    need(commit==data['source_commit'],'Mixed source-link revisions');item=dict(commit=commit,file=rel)
                    if a.enforce_committed_links:
                        r=subprocess.run(['git','cat-file','-e',commit+':'+rel],cwd=a.repository,capture_output=True)
                        need(r.returncode==0,'Source link absent from reviewed Git revision: '+rel);item['committed']=True
                    link_rows.append(item)
            for name,selector in [('top','header'),('source','#sources details'),('canonical','.canonical-claim'),('korean','#korean')]:
                target=page.locator(selector).first;target.scroll_into_view_if_needed();q=a.out/(label+'-'+name+'.png')
                if name in ['source','canonical']:target.screenshot(path=str(q))
                else:page.screenshot(path=str(q))
                screens.append(dict(file=q.name,sha256=sha(q)))
            overflow=page.locator('.formula').evaluate_all('(xs)=>xs.map((x,i)=>({i,width:x.clientWidth,scroll:x.scrollWidth})).filter(x=>x.scroll>x.width+5)')
            horizontal=dict(applicable=bool(overflow))
            if overflow:
                wide=page.locator('.formula').nth(overflow[0]['i']);wide.evaluate('e=>e.scrollLeft=0');wide.focus();page.keyboard.press('ArrowRight');page.wait_for_timeout(300);horizontal['scroll_after_arrow_right']=wide.evaluate('e=>e.scrollLeft');need(horizontal['scroll_after_arrow_right']>0,'Wide formula did not scroll with keyboard')
            rows.append(dict(label=label,dimensions=dims,keyboard_disclosure=True,formula_keyboard_focus=True,horizontal_formula_keyboard=horizontal,network_requests=[],browser=browser.version))
            context.close()
        browser.close()
    need(sha(a.report)==sha(frozen),'Report changed during QA')
    result=dict(status='PASS_OFFLINE_STATIC_MATH_PRESENTATION_AND_REQUESTED_LINK_CHECKS_NOT_PROOF_ACCEPTANCE',report_sha256=sha(frozen),data_sha256=sha(a.data),source_commit=data['source_commit'],complete_result_data=data['completion']['complete'],committed_link_check=a.enforce_committed_links,source_links=link_rows,rows=rows,screenshots=screens,actual_browser_binary=browser_identity,playwright=importlib.metadata.version('playwright'),controller_sha256=sha(Path(__file__)),mathematical_acceptance=False,delivery_verified=False)
    publish(a.out/'RESULT.json',result);print(json.dumps(dict(status=result['status'],math=rows[0]['dimensions']['math'],canonical=29,source_links=len(link_rows),committed=a.enforce_committed_links,report_sha256=result['report_sha256'])))
if __name__=='__main__':main()
