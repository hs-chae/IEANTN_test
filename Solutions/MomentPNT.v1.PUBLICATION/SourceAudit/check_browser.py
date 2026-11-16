"""Offline all80MathML/mobile/desktop/keyboard/local-link gate."""
from pathlib import Path
import argparse,hashlib,json,re,urllib.parse
from playwright.sync_api import sync_playwright
B=Path(__file__).resolve().parent
def need(ok,message):
 if not ok:raise ValueError(message)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 report=B/'PRIMARY14_AND_SUPPORT_SOURCE_AUDIT_V4.html';out=a.out.resolve()
 need(not out.exists()and out.is_relative_to(B),'Fresh owned output');out.mkdir(parents=True)
 text=report.read_text();links=re.findall(r'href="([^"]+)"',text);checked=[]
 for href in links:
  url=urllib.parse.urlparse(href)
  if not url.scheme:
   path=report.parent/urllib.parse.unquote(url.path);need(path.is_file(),'Missing local evidence link '+href)
   checked.append({'href':href,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
 need(len(checked)==65,'Exactsource/evidence links')
 rows=[]
 with sync_playwright()as p:
  browser=p.chromium.launch(headless=True)
  for width in [390,1440]:
   page=browser.new_page(viewport={'width':width,'height':950});errors=[]
   page.on('pageerror',lambda e:errors.append(str(e)))
   page.route('**/*',lambda route:route.continue_()if route.request.url.startswith('file:')else route.abort())
   page.goto(report.as_uri(),wait_until='load');page.locator('details').evaluate_all('(items)=>items.forEach(e=>e.open=true)')
   row=page.evaluate('''()=>({width:innerWidth,documentWidth:document.documentElement.scrollWidth,
    mathCount:document.querySelectorAll('math').length,
    allObjectRows:document.querySelectorAll('details.object').length,
    badBinary:[...document.querySelectorAll('mfrac,msup,msub,mroot')].filter(e=>e.children.length!==2).length,
    badTernary:[...document.querySelectorAll('msubsup')].filter(e=>e.children.length!==3).length,
    scrollableMath:[...document.querySelectorAll('.math-scroll')].filter(e=>e.scrollWidth>e.clientWidth).length,
    inaccessibleMath:[...document.querySelectorAll('.math-scroll')].filter(e=>e.scrollWidth>e.clientWidth&&(getComputedStyle(e).overflowX!=='auto'||e.tabIndex!==0)).length})''')
   page.keyboard.press('Tab');row['keyboard_focus']=page.evaluate('document.activeElement.tagName')
   img=out/(str(width)+'.png');page.screenshot(path=str(img),full_page=False)
   row.update(errors=errors,screenshot_sha256=hashlib.sha256(img.read_bytes()).hexdigest());rows.append(row)
   (out/'PARTIAL.json').write_text(json.dumps(rows,indent=2)+'\n')
   need(row['documentWidth']<=width and row['mathCount']==83 and row['allObjectRows']==45 and
    not row['badBinary']and not row['badTernary']and not row['inaccessibleMath']and not errors and
    row['keyboard_focus']not in['BODY','HTML'],'Actual offline geometry/math/keyboard')
   page.close()
  browser.close()
 receipt={'status':'PASS_ACTUAL_OFFLINE_ALL83_MATH45_OBJECTS_MOBILE_DESKTOP_LINK_KEYBOARD',
  'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest(),'rows':rows,'local_links':checked,
  'qualification':'Long formulas remain fully readable in labelled keyboard-focusable horizontal scroll panels; this is not a claim every full formula fits mobile width. No network dependency for report rendering.'}
 tmp=out/'RECEIPT.pending';tmp.write_text(json.dumps(receipt,indent=2)+'\n');tmp.replace(out/'RECEIPT.json');print(out/'RECEIPT.json')
if __name__=='__main__':main()
