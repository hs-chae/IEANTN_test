"""Pinned standalone HTML checks using installed Playwright/Chromium only.

--check parses source/configuration only. --execute requires the actual registered
64GiB/eight-CPU frame. Screenshots and geometry checks do not prove mathematics.
"""
from pathlib import Path
from html.parser import HTMLParser
import argparse,hashlib,importlib.metadata,json,os,re,resource,sys
sys.dont_write_bytecode=True
S=Path(__file__).resolve().parents[1]
VIEWPORTS=[{'width':1440,'height':1000},{'width':390,'height':844}]

def need(c,m):
    if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p):return {'path':str(p),'sha256':sha(p)}
def load(p):
    def pairs(rows):
        d={}
        for k,v in rows:
            need(k not in d,'duplicate configuration key');d[k]=v
        return d
    return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(ValueError('nonfinite JSON')))
def atomic(p,d):
    t=p.with_name('.'+p.name+'.pending')
    with t.open('x') as f:json.dump(d,f,indent=2,allow_nan=False);f.write('\n')
    os.link(t,p);t.unlink()

class SourceMarkup(HTMLParser):
    def __init__(self):super().__init__();self.csp=[];self.math=0;self.external_scripts=[]
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if tag=='meta' and a.get('http-equiv','').casefold()=='content-security-policy':self.csp.append(a.get('content',''))
        if tag=='math':self.math+=1
        if tag=='script' and 'src' in a:self.external_scripts.append(a['src'])

def configuration(path):
    path=path.resolve();need(path.is_file() and path.is_relative_to(S),'owned configuration required')
    d=load(path);need(d.get('schema')=='FINAL_PUBLICATION_BROWSER_CONFIG_V1','browser configuration schema')
    browser=d['browser'];binary=Path(browser['path'])
    need(binary.is_absolute() and binary.is_file() and sha(binary)==browser['sha256'],'installed browser binary differs')
    need(importlib.metadata.version('playwright')==browser['playwright_version'],'installed Playwright version differs')
    rows=d['artifacts'];need(isinstance(rows,list) and len(rows)==2 and {r['name'] for r in rows}=={'final-report','unscored-paper'},'exact final report and separate paper required')
    for row in rows:
        p=Path(row['path']);need(p.is_absolute() and p.is_file() and not p.is_symlink() and p.resolve()==p and p.is_relative_to(S) and p.suffix=='.html' and sha(p)==row['sha256'],'pinned standalone HTML differs')
        source=p.read_text();mark=SourceMarkup();mark.feed(source)
        need(len(mark.csp)==1 and re.search(r"(?:^|;)\s*default-src\s+'none'\s*(?:;|$)",mark.csp[0]),'one CSP default-src none required')
        need(not mark.external_scripts and mark.math>0,'static MathML and no external scripts required')
        need(not re.search(r'\\\(|\\\[|\$\$|\\(?:frac|begin|operatorname)\b|\$[A-Za-z\\][^$\n]{0,300}\$',source),'unrendered mathematical TeX delimiter/command')
        selectors=row.get('focus_selectors',[]);need(isinstance(selectors,list) and len(selectors)<=4 and all(isinstance(x,str) and 0<len(x)<200 for x in selectors),'bounded focus selectors required')
    return d

def frame(cpus,unit):
    rows=[x[3:] for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::')]
    need(len(rows)==1 and rows[0].endswith('/'+unit),'registered browser cgroup required')
    group=Path('/sys/fs/cgroup')/rows[0].lstrip('/');maximum=(group/'memory.max').read_text().strip()
    need(maximum!='max' and 0<int(maximum)<=64*1024**3 and (group/'memory.swap.max').read_text().strip()=='0','registered64GiB zero-swap frame required')
    need(sorted(os.sched_getaffinity(0))==cpus and len(cpus)==8,'exact reserved eight-CPU affinity required')
    need(resource.getrlimit(resource.RLIMIT_NOFILE)[0]==65536,'browser file descriptor limit differs')
    return {'cgroup':rows[0],'memory_max_bytes':int(maximum),'swap_max_bytes':0,'affinity':cpus,'FD_limit':65536}

GEOMETRY="""() => {
 const visible=e=>{let r=e.getBoundingClientRect(),s=getComputedStyle(e);return r.width>0&&r.height>0&&s.display!=='none'&&s.visibility!=='hidden'};
 const bounds=e=>{let r=e.getBoundingClientRect();return {x:r.x,y:r.y,width:r.width,height:r.height}};
 const scrollParent=e=>{for(let a=e.parentElement;a&&a!==document.body;a=a.parentElement){let s=getComputedStyle(a),r=a.getBoundingClientRect();if(['auto','scroll'].includes(s.overflowX)&&a.scrollWidth>a.clientWidth+1&&r.left>=-1&&r.right<=innerWidth+1)return a}return null};
 let maths=[...document.querySelectorAll('math')],bad=maths.filter(e=>!visible(e)).map((e,i)=>i);
 let outside=[...document.querySelectorAll('math,table,pre,figure')].filter(e=>{let r=e.getBoundingClientRect();return visible(e)&&(r.left < -1||r.right>innerWidth+1)&&!scrollParent(e)}).map(e=>({tag:e.tagName,bounds:bounds(e)}));
 let tables=[...document.querySelectorAll('table')].map(e=>{let a=scrollParent(e);return {table:bounds(e),scroll:a?{id:a.dataset.browserTableId,tabIndex:a.tabIndex,clientWidth:a.clientWidth,scrollWidth:a.scrollWidth}:null}});
 return {title:document.title,viewport:innerWidth,documentWidth:document.documentElement.scrollWidth,bodyWidth:document.body.getBoundingClientRect().width,mathCount:maths.length,zeroOrHiddenMath:bad,uncontainedWideElements:outside,tables,missingImages:[...document.images].filter(i=>!i.complete||!i.naturalWidth).length,nativeMathML:typeof MathMLElement!=='undefined'};
}"""

def render(config,out,resource_frame):
    from playwright.sync_api import sync_playwright
    need(not out.exists(),'fresh browser artifact output required');out.mkdir(parents=True);(out/'tmp').mkdir()
    os.environ['TMPDIR']=str(out/'tmp');os.environ['PLAYWRIGHT_SKIP_BROWSER_DOWNLOAD']='1'
    rows=[]
    with sync_playwright() as pw:
        browser=pw.chromium.launch(headless=True,executable_path=config['browser']['path'],args=['--disable-background-networking','--disable-component-update','--no-first-run'])
        try:
            for artifact in config['artifacts']:
                p=Path(artifact['path']);need(sha(p)==artifact['sha256'],'HTML changed before render')
                for viewport in VIEWPORTS:
                    label=artifact['name']+'-'+str(viewport['width']);context=browser.new_context(viewport=viewport,device_scale_factor=1,offline=True,service_workers='block')
                    requests=[];errors=[];console=[]
                    def route(request):
                        url=request.request.url
                        if url==p.as_uri() or url.startswith('data:') or url=='about:blank':request.continue_()
                        else:requests.append(url);request.abort()
                    context.route('**/*',route);page=context.new_page();page.on('pageerror',lambda e:errors.append(str(e)));page.on('console',lambda e:console.append(e.text) if e.type=='error' else None)
                    try:
                        page.goto(p.as_uri(),wait_until='load',timeout=30000);page.wait_for_timeout(150)
                        top=out/(label+'-top.png');page.screenshot(path=str(top),full_page=False)
                        initial=page.evaluate("() => ({math:document.querySelectorAll('math').length,visible:[...document.querySelectorAll('math')].filter(e=>{let r=e.getBoundingClientRect();return r.width>0&&r.height>0}).length,closedDetails:[...document.querySelectorAll('details:not([open])')].length})")
                        need(initial['visible']>0,'no MathML visible on first-use page')
                        opened=page.evaluate("() => {let ds=[...document.querySelectorAll('details:not([open])')];ds.forEach(e=>e.open=true);return ds.length}")
                        page.evaluate("() => {let n=0;for(let a of document.querySelectorAll('*')){let s=getComputedStyle(a);if(['auto','scroll'].includes(s.overflowX)&&a.scrollWidth>a.clientWidth+1)a.dataset.browserTableId='scroll-'+n++}}")
                        geometry=page.evaluate(GEOMETRY)
                        need(geometry['nativeMathML'] and geometry['mathCount']>0 and not geometry['zeroOrHiddenMath'],'native MathML geometry failed')
                        need(geometry['documentWidth']<=viewport['width']+1 and geometry['bodyWidth']<=viewport['width']+1 and not geometry['uncontainedWideElements'],'uncontained page/content horizontal overflow')
                        need(geometry['missingImages']==0,'missing inline image')
                        keyboard=[];seen=set()
                        for table in geometry['tables']:
                            sc=table['scroll']
                            if not sc or sc['id'] in seen:continue
                            seen.add(sc['id']);need(sc['tabIndex']>=0,'wide table container is not keyboard focusable')
                            loc=page.locator('[data-browser-table-id="'+sc['id']+'"]');loc.focus();page.keyboard.press('Shift+Tab');page.keyboard.press('Tab')
                            state=page.evaluate("() => {let a=document.activeElement,s=getComputedStyle(a);return {id:a.dataset.browserTableId,outline:s.outlineStyle,outlineWidth:parseFloat(s.outlineWidth),shadow:s.boxShadow,scrollLeft:a.scrollLeft}}")
                            need(state['id']==sc['id'] and ((state['outline']!='none' and state['outlineWidth']>0) or state['shadow']!='none'),'table keyboard focus/order/ring failed')
                            loc.evaluate('(e)=>e.scrollLeft=0');page.keyboard.press('ArrowRight');page.wait_for_timeout(150)
                            need(loc.evaluate('(e)=>e.scrollLeft')>0,'wide table does not scroll with keyboard')
                            loc.evaluate('(e)=>e.scrollLeft=0');keyboard.append(state)
                        anchors=page.evaluate("() => [...document.querySelectorAll('a[href^=\"#\"]')].filter(a=>a.getAttribute('href').length>1).map(a=>({href:a.getAttribute('href'),exists:!!document.getElementById(decodeURIComponent(a.hash.slice(1)))}))")
                        need(all(x['exists'] for x in anchors),'broken local first-use anchor')
                        need(artifact['name']!='final-report' or anchors,'main report needs local navigation anchors')
                        anchor_test=None
                        if anchors:
                            page.goto(p.as_uri(),wait_until='load');found=False
                            for _ in range(min(500,page.locator('a[href],button,input,select,textarea,[tabindex]').count()+5)):
                                page.keyboard.press('Tab')
                                focus=page.evaluate("() => {let a=document.activeElement;return {tag:a.tagName,href:a.getAttribute('href')}}")
                                if focus['tag']=='A' and focus['href'] and focus['href'].startswith('#') and len(focus['href'])>1:found=True;break
                            need(found,'local navigation anchor not reachable by keyboard')
                            page.keyboard.press('Enter');page.wait_for_timeout(100)
                            anchor_test=page.evaluate("() => {let e=document.getElementById(decodeURIComponent(location.hash.slice(1))),r=e&&e.getBoundingClientRect();return {hash:location.hash,targetTop:r&&r.top,targetHeight:r&&r.height}}")
                            need(anchor_test['hash'] and anchor_test['targetTop'] is not None and -2<=anchor_test['targetTop']<viewport['height'],'keyboard first-use anchor did not expose target')
                        page.evaluate("() => {for(let d of document.querySelectorAll('details'))d.open=true}")
                        selectors=artifact.get('focus_selectors') or ['math']
                        shots=[pin(top)]
                        for i,selector in enumerate(selectors):
                            loc=page.locator(selector).first;need(loc.count()>0,'source/math screenshot selector missing: '+selector);loc.scroll_into_view_if_needed();page.wait_for_timeout(80)
                            shot=out/(label+'-focus-'+str(i+1)+'.png');page.screenshot(path=str(shot),full_page=False);shots.append(pin(shot))
                        need(not requests and not errors and not console,'external request/script/CSP console error')
                        rows.append({'artifact':artifact['name'],'artifact_pin':{'path':str(p),'sha256':artifact['sha256']},'viewport':viewport,'first_use':initial,'details_opened_for_full_math_check':opened,'geometry':geometry,'wide_table_keyboard_checks':keyboard,'local_anchor_keyboard_check':anchor_test,'external_page_request_attempts':requests,'page_errors':errors,'console_errors':console,'screenshots':shots})
                        atomic(out/(label+'.json'),rows[-1])
                    finally:context.close()
                need(sha(p)==artifact['sha256'],'HTML changed during browser check')
        finally:browser.close()
    result={'schema':'FINAL_PUBLICATION_BROWSER_CHECK_RECEIPT_V1','status':'PASS_PINNED_STANDALONE_DESKTOP_MOBILE_REPORT_RENDER','source':pin(Path(__file__).resolve()),'configuration':config,'rows':rows,'resource_frame':resource_frame,'installed_browser_only':True,'downloads_requested':0,'external_page_requests_observed':False,'model_calls':0,'mathematical_truth_or_PV_assessed':False,'limitation':'Page requests, static layout and screenshots are checked. This is not a proof of mathematical source contracts or all host network behavior.'}
    atomic(out/'RECEIPT.json',result);print(json.dumps({'status':result['status'],'receipt':pin(out/'RECEIPT.json')}))

def main():
    p=argparse.ArgumentParser(description=__doc__,allow_abbrev=False);p.add_argument('--config',type=Path,required=True)
    modes=p.add_mutually_exclusive_group(required=True);modes.add_argument('--check',action='store_true');modes.add_argument('--execute',action='store_true')
    p.add_argument('--out',type=Path);p.add_argument('--cpus');p.add_argument('--unit');a=p.parse_args()
    config=configuration(a.config)
    if a.check:print(json.dumps({'status':'PASS_PINNED_BROWSER_ARTIFACT_SOURCE_CHECK_NO_BROWSER_STARTED','configuration':config,'model_calls':0}));return
    need(a.out is not None and a.cpus and a.unit,'registered browser output/affinity/unit required')
    cpus=[int(x) for x in a.cpus.split(',')];resource_frame=frame(cpus,a.unit);render(config,a.out.resolve(),resource_frame)

if __name__=='__main__':main()
