from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import unquote,urlparse
from playwright.sync_api import sync_playwright
import hashlib,json,os
B=Path(__file__).resolve().parent
class Audit(HTMLParser):
 def __init__(self):super().__init__();self.links=[];self.stack=[];self.bad=[]
 def handle_starttag(self,t,attrs):
  d=dict(attrs)
  if t=='a' and 'href'in d:self.links.append(d['href'])
  if self.stack:self.stack[-1][1]+=1
  if t not in ['meta','br','hr','img','input','link']:self.stack.append([t,0])
 def handle_endtag(self,t):
  for i in range(len(self.stack)-1,-1,-1):
   if self.stack[i][0]==t:
    tag,count=self.stack[i]
    if tag in ['mfrac','msup','msub']and count!=2:self.bad.append((tag,count))
    self.stack=self.stack[:i];break

def main():
 out=B/'pi-psi300-browser-v3';out.mkdir(exist_ok=False);p=B/'SOURCE_PI_PSI300_AND_PRIME_RICH_REPORT_V2.html';text=p.read_text();audit=Audit();audit.feed(text)
 if audit.bad:raise ValueError('bad math arity '+repr(audit.bad))
 for h in audit.links:
  u=urlparse(h)
  if not u.scheme and not (B/unquote(u.path)).is_file():raise ValueError('missing link '+h)
 if '$$'in text or '\\('in text or '\\['in text:raise ValueError('raw TeX delimiter')
 rows=[]
 with sync_playwright()as pw:
  browser=pw.chromium.launch(headless=True)
  for width in [390,1280]:
   page=browser.new_page(viewport=dict(width=width,height=1000));page.route('http://**/*',lambda r:r.abort());page.route('https://**/*',lambda r:r.abort());page.goto(p.as_uri());page.evaluate('document.fonts.ready')
   if page.evaluate('document.documentElement.scrollWidth > innerWidth'):raise ValueError('body overflow '+str(width))
   overflow=page.locator('.formula').evaluate_all('(xs)=>xs.map((x,i)=>({i,scroll:x.scrollWidth,width:x.clientWidth})).filter(x=>x.scroll>x.width+1)')
   if overflow:raise ValueError('formula overflow '+str(width)+repr(overflow))
   page.screenshot(path=str(out/(str(width)+'-top.png')))
   for i in [1,3,5]:page.locator('article').nth(i).screenshot(path=str(out/(str(width)+'-card'+str(i)+'.png')))
   page.keyboard.press('Tab');focus=page.evaluate('document.activeElement.tagName')
   if focus!='A':raise ValueError('first keyboard action not link')
   rows.append(dict(width=width,body_overflow=False,formula_overflow=False,first_tab='A',formula_count=page.locator('.formula').count()));page.close()
  browser.close()
 d=dict(status='PASS_OFFLINE_STATIC_MATH_ALL_LOCAL_LINKS_MOBILE_DESKTOP_KEYBOARD',report_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),local_links=len(audit.links),views=rows,mathematical_proof=False)
 temp=out/'RECEIPT.pending';temp.write_text(json.dumps(d,indent=2)+'\n');os.replace(temp,out/'RECEIPT.json');print(d['status'])
if __name__=='__main__':main()
