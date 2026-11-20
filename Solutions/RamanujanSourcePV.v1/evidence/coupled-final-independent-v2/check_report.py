from pathlib import Path
import hashlib,json
from playwright.sync_api import sync_playwright
S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1');report=S/'evidence/coupled-final-independent-v2/REPORT.html';out=Path('/data/ivy-ramanujan-source-pv-20261119/coupled-final-independent-audit-v1/browser-v3');out.mkdir(exist_ok=False)
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
identity=sha(report);rows=[]
with sync_playwright()as api:
 browser=api.chromium.launch(headless=True)
 for width,name in [(390,'mobile'),(1280,'desktop')]:
  page=browser.new_page(viewport=dict(width=width,height=900));network=[];errors=[];page.on('request',lambda r:network.append(r.url)if r.url.startswith(('http:','https:'))else None);page.on('pageerror',lambda e:errors.append(str(e)));page.goto(report.as_uri(),wait_until='load');page.evaluate('document.fonts.ready');state=page.evaluate(r'''() => ({width:innerWidth,documentWidth:document.documentElement.scrollWidth,math:[...document.querySelectorAll('math')].map(m=>({width:m.getBoundingClientRect().width,height:m.getBoundingClientRect().height})),raw:/\\\(|\\\[|\$[^$]+\$/.test(document.body.innerText),cards:document.querySelectorAll('article').length})''');need(state['width']==state['documentWidth']==width,'no globaloverflow');need(len(state['math'])==19 and all(v['height']>0 and v['width']>0 for v in state['math'])and not state['raw'],'actualstaticMathML');need(not network and not errors,'offlinestandalone');page.screenshot(path=str(out/(name+'.png')),full_page=True);rows.append(dict(mode=name,state=state,network=network,errors=errors,screenshot_sha256=sha(out/(name+'.png'))));page.close()
 browser.close()
need(sha(report)==identity,'reportbytesunchanged');r=dict(status='PASS_ACTUAL_OFFLINE_MOBILE_DESKTOP_MATHML',report_sha256=identity,records=rows);(out/'RESULT.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status=r['status'],result=str(out/'RESULT.json'))))
