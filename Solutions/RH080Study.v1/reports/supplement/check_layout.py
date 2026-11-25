#!/usr/bin/env python3
"""Offline viewport/font/keyboard checks; proof acceptance is separate."""
from pathlib import Path
from playwright.sync_api import sync_playwright
import argparse,hashlib,json,re,sys,xml.etree.ElementTree as ET,base64,os,tempfile
ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--render-package',type=Path);ap.add_argument('--browser-executable',type=Path);a=ap.parse_args()
if a.render_package:sys.path.insert(0,str(a.render_package))
from fontTools.ttLib import TTFont
import io
S=Path(__file__).resolve().parent;D=a.out.resolve()
if D.exists()or S==D or S in D.parents:raise ValueError('Use a fresh experiment-owned output directory outside the report sources')
D.mkdir(parents=True);rows=[]
font=TTFont(io.BytesIO(base64.b64decode((S/'STIXGeneral.ttf.base64.txt').read_text())));covered=font.getBestCmap();missing={}
for filename in ['RH080_PAPER_SUMMARY_KO.html','PAPER_READY_EN.html']:
 text=(S/filename).read_text();codes=set()
 for math in re.findall(r'<math\b.*?</math>',text,re.S):
  codes.update(ord(c)for c in ''.join(ET.fromstring(math).itertext())if not c.isspace())
 missing[filename]=[hex(c)for c in sorted(codes)if c not in covered]
 if missing[filename]:raise ValueError(('font missing actual math text',missing))
with sync_playwright()as pw:
 b=pw.chromium.launch(headless=True,args=['--no-sandbox'],**({'executable_path':str(a.browser_executable)}if a.browser_executable else{}))
 for filename in ['RH080_PAPER_SUMMARY_KO.html','PAPER_READY_EN.html']:
  for label,width,height in [('narrow',320,780),('mobile',390,844),('desktop',1280,900)]:
   p=b.new_page(viewport={'width':width,'height':height});requests=[]
   p.on('request',lambda q:requests.append({'scheme':q.url.split(':',1)[0],'url_sha256':hashlib.sha256(q.url.encode()).hexdigest()}))
   p.goto((S/filename).as_uri());p.wait_for_timeout(300)
   data=p.evaluate('''()=>({lang:document.documentElement.lang,math:document.querySelectorAll('math').length,rootWidth:document.documentElement.scrollWidth,view:innerWidth,brokenNav:[...document.querySelectorAll('nav a')].filter(a=>!document.querySelector(a.getAttribute('href'))).length,mathVisible:[...document.querySelectorAll('math')].every(m=>m.getBoundingClientRect().height>8),scripts:document.scripts.length,fontLoaded:document.fonts.check('17px RH080Math')})''')
   if data['rootWidth']>data['view']+1 or data['brokenNav']or not data['mathVisible']or data['scripts']or not data['fontLoaded']:raise ValueError((filename,label,data))
   if any(x['scheme']in ['http','https']for x in requests):raise ValueError('external asset request')
   # Every navigation link must actually take focus and reach its declared section.
   nav=p.locator('nav a');anchors=[]
   for i in range(nav.count()):
    a=nav.nth(i);target=a.get_attribute('href');a.focus()
    if not a.evaluate('(e)=>e===document.activeElement'):raise ValueError('keyboard navigation focus')
    a.press('Enter');p.wait_for_timeout(10);anchors.append(target)
    if p.evaluate('location.hash')!=target:raise ValueError('anchor navigation')
   scrollers=p.locator('.formula');tested=0
   if label in ['narrow','mobile']:
    for i in range(scrollers.count()):
     e=scrollers.nth(i)
     if e.evaluate('(e)=>e.scrollWidth>e.clientWidth+20'):
      e.scroll_into_view_if_needed();e.focus();e.evaluate('(e)=>e.scrollLeft=0');e.press('ArrowRight');p.wait_for_timeout(180)
      if e.evaluate('(e)=>e.scrollLeft')<=0:raise ValueError('formula keyboard scrolling failed')
      tested+=1
    if not tested:raise ValueError('no wide formula keyboard case')
   p.evaluate('scrollTo(0,0)');p.screenshot(path=str(D/(filename.replace('.html','')+'_'+label+'.png')))
   p.locator('section').nth(3).scroll_into_view_if_needed();p.screenshot(path=str(D/(filename.replace('.html','')+'_'+label+'_math.png')))
   rows.append({'file':filename,'viewport':label,'data':data,'request_schemes_and_hashes':requests,'anchor_targets':anchors,'keyboard_wide_equations_tested':tested,'html_sha256':hashlib.sha256((S/filename).read_bytes()).hexdigest()});p.close()
 b.close()
r={'status':'PASS_SIX_OFFLINE_FONT_MATHML_MOBILE_DESKTOP_KEYBOARD_AND_ANCHOR_CASES','rows':rows,'font_actual_MathML_codepoints_missing':missing,'known_previous_visual_failure':'Before explicitmathfont,Greekpi renderedas missingglyphsquare despiteDOM-onlychecksPASS; preservedv1screenshots. AfterunmodifiedSTIXfont,actualvisualinspectionconfirmedpiandintegralsrender.','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
fd,name=tempfile.mkstemp(prefix='.layout-',dir=D)
temporary=Path(name)
try:
 with os.fdopen(fd,'w')as out:json.dump(r,out,indent=2,allow_nan=False);out.write('\n')
 os.link(temporary,D/'RESULT.json')
finally:temporary.unlink(missing_ok=True)
print(r['status'])
