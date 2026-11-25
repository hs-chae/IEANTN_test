#!/usr/bin/env python3
"""Actual offline browser QA of the single report; no Python assert acceptance."""
import argparse, base64, hashlib, importlib.metadata, json, os, re, subprocess, sys, tempfile, time
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit

BROWSER = '/ryu/hyunsik/.cache/ms-playwright/chromium_headless_shell-1243/chrome-headless-shell-linux64/chrome-headless-shell'

def need(value, message):
    if not value:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read_json(path):
    def pairs(rows):
        result={}
        for k,v in rows:
            need(k not in result, 'Duplicate JSON key: '+k)
            result[k]=v
        return result
    def bad_constant(value):
        raise ValueError('Non-finite JSON constant: '+value)
    return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=bad_constant)

def norm(text):
    return ' '.join(text.split())

def atomic(path, value):
    need(not path.exists(), 'Fresh receipt required')
    fd, name = tempfile.mkstemp(prefix='.receipt-', dir=path.parent)
    q = Path(name)
    try:
        with os.fdopen(fd, 'w') as f:
            json.dump(value, f, indent=2, ensure_ascii=False, allow_nan=False)
            f.write('\n'); f.flush(); os.fsync(f.fileno())
        os.link(q, path)
    finally:
        q.unlink()

class SourceHTML(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.paragraphs, self.current, self.math, self.scripts = [], None, 0, 0
    def handle_starttag(self, tag, attrs):
        if tag == 'script': self.scripts += 1
        if tag == 'math': self.math += 1
        if tag == 'p':
            need(self.current is None, 'Nested source paragraphs')
            self.current = []
    def handle_data(self, text):
        if self.current is not None: self.current.append(text)
    def handle_endtag(self, tag):
        if tag == 'p':
            need(self.current is not None, 'Unmatched source paragraph')
            self.paragraphs.append(norm(''.join(self.current))); self.current = None

def contrast_rgb(foreground,background):
    def rgb(value):
        n=[float(x) for x in re.findall(r'[0-9.]+',value)]
        need(len(n) in [3,4] and all(0<=x<=255 for x in n[:3]),'Unexpected browser color syntax')
        return [x/255 for x in n[:3]]
    def luminance(row):
        v=[x/12.92 if x<=.04045 else ((x+.055)/1.055)**2.4 for x in row]
        return .2126*v[0]+.7152*v[1]+.0722*v[2]
    a,b=sorted([luminance(rgb(foreground)),luminance(rgb(background))])
    return (b+.05)/(a+.05)

def viewport_list(text):
    rows = []
    for item in text.split(','):
        need(re.fullmatch(r'[0-9]+x[0-9]+', item) is not None, 'Invalid viewport syntax')
        w, h = map(int, item.split('x'))
        need(200 <= w <= 4096 and 200 <= h <= 4096, 'Invalid viewport dimensions')
        rows.append(dict(width=w, height=h))
    need(len(rows) > 0 and len(rows) <= 6, 'Invalid viewport population')
    return rows

def source_links(page, metadata, repository, enforce):
    links = page.locator('a[href]').evaluate_all('(xs)=>xs.map(x=>x.href)')
    prefix = 'https://github.com/hs-chae/IEANTN_test/blob/'
    rows = []
    for url in sorted(set(x for x in links if x.startswith(prefix))):
        tail = unquote(urlsplit(url).path.split('/blob/', 1)[1])
        commit, path = tail.split('/', 1)
        need(commit == metadata['source_revision'], 'Inconsistent displayed source-link revision')
        row = dict(commit=commit, path=path)
        if repository is not None:
            r = subprocess.run(['git', 'cat-file', '-e', commit + ':' + path], cwd=repository, capture_output=True)
            row['present_in_local_git_object'] = r.returncode == 0
        rows.append(row)
    if enforce:
        need(repository is not None, 'Source-link gate requires --repository')
        need(rows and all(x.get('present_in_local_git_object') for x in rows), 'Source-link release gate failed')
    return dict(enforced=enforce, source_revision=metadata['source_revision'], links=rows,
                remote_publication_verified=False)

def native_disclosure(page,label):
    summary=page.locator('summary').filter(has_text=re.compile('^'+re.escape(label)+'$'))
    need(summary.count()==1,'Missing/duplicate native disclosure: '+label)
    details=summary.locator('xpath=..')
    need(details.evaluate('e=>e.tagName')=='DETAILS','Disclosure is not native details: '+label)
    return summary,details

def actual_fonts(page):
    client = page.context.new_cdp_session(page)
    client.send('DOM.enable'); client.send('CSS.enable'); client.send('DOM.getDocument', {'depth': -1, 'pierce': True})
    rows = []
    for char in ['π', 'ϑ', 'θ']:
        expr = 'Array.from(document.querySelectorAll("math mi")).find(x=>x.textContent===' + json.dumps(char) + ')'
        obj = client.send('Runtime.evaluate', dict(expression=expr))['result']
        if 'objectId' not in obj:
            rows.append(dict(character=char, present=False)); continue
        node = client.send('DOM.requestNode', dict(objectId=obj['objectId']))['nodeId']
        fonts = client.send('CSS.getPlatformFontsForNode', dict(nodeId=node))['fonts']
        rows.append(dict(character=char, present=True, actual_platform_fonts=fonts))
    client.detach()
    return rows

def run(a, output, metadata, parsed, frozen, original_sha):
    from playwright.sync_api import sync_playwright
    need(importlib.metadata.version('playwright') == '1.62.0', 'Pinned Playwright version differs')
    problems, results, screenshots, requests, errors = [], [], [], [], []
    def check(ok, message):
        if not ok: problems.append(message)
    with sync_playwright() as pw:
        browser = pw.chromium.launch(executable_path=str(a.browser), headless=True)
        version = browser.version
        for vp in a.viewports:
            label = str(vp['width']) + 'x' + str(vp['height'])
            context = browser.new_context(viewport=vp, is_mobile=vp['width'] <= 640,
                                          has_touch=vp['width'] <= 640, offline=True)
            page = context.new_page()
            def request_seen(r):
                u = r.url; scheme = urlsplit(u).scheme
                requests.append(dict(viewport=label, scheme=scheme,
                                     url=u if scheme != 'data' else 'data:SHA256:' + hashlib.sha256(u.encode()).hexdigest()))
            page.on('request', request_seen)
            page.on('pageerror', lambda e: errors.append(str(e)))
            page.goto(frozen.as_uri(), wait_until='load')
            page.evaluate('document.fonts.ready')
            check(page.locator('script').count() == 0, label + ': script in static report')
            check(page.locator('math').count() == parsed.math, label + ': MathML population changed')
            check(page.locator('merror,parsererror').count() == 0, label + ': MathML/parser error')
            paragraphs = [norm(x) for x in page.locator('p').all_text_contents()]
            check(paragraphs == parsed.paragraphs, label + ': browser repaired/lost source prose HTML')
            text = page.locator('body').inner_text()
            check('�' not in text and not re.search(r'\\[\[(]|\\begin\{', text), label + ': damaged/raw math prose')
            dims = page.evaluate('''()=>({viewport:innerWidth,root:document.documentElement.scrollWidth,
                body:document.body.scrollWidth,rootHeight:document.documentElement.scrollHeight,
                loadedMathFont:document.fonts.check('20px RH080Math','πϑθ')})''')
            check(dims['viewport'] == vp['width'], label + ': mobile layout viewport expanded beyond requested width')
            check(dims['root'] <= vp['width'] + 1, label + ': page-level horizontal overflow')
            check(dims['body'] <= vp['width'] + 1, label + ': body horizontal overflow')
            check(dims['loadedMathFont'], label + ': embedded math font unavailable offline')
            header_colors=page.locator('header details .fine').evaluate('e=>({foreground:getComputedStyle(e).color,background:getComputedStyle(e.closest("header")).backgroundColor,fontSize:getComputedStyle(e).fontSize})')
            header_colors['contrast_ratio']=contrast_rgb(header_colors['foreground'],header_colors['background'])
            check(header_colors['contrast_ratio']>=4.5,label+': header source-pin contrast below4.5')
            header_all_colors=page.locator('header .fine').evaluate_all('xs=>xs.map(e=>({foreground:getComputedStyle(e).color,background:getComputedStyle(e.closest("header")).backgroundColor,text:e.textContent}))')
            for row in header_all_colors:
                row['contrast_ratio']=contrast_rgb(row['foreground'],row['background'])
                check(row['contrast_ratio']>=4.5,label+': header muted text contrast below4.5')
            visible_math=page.locator('math').evaluate_all('xs=>xs.map(e=>{let r=e.getBoundingClientRect();let s=getComputedStyle(e);return{width:r.width,height:r.height,display:s.display,visibility:s.visibility}})')
            check(all(x['width']>0 and x['height']>0 and x['display']!='none' and x['visibility']!='hidden' for x in visible_math),label+': hidden or zero-size MathML')
            path=output/(label+'-first-view.png');page.screenshot(path=str(path));screenshots.append(path)
            meta_summary,meta_details=native_disclosure(page,'Source revision and branch')
            contents_summary,contents_details=native_disclosure(page,'Detailed contents and evidence')
            first_use=page.evaluate('''()=>({metadataInitiallyOpen:[...document.querySelectorAll('header details')].some(e=>e.open),summaryBeforeContents:!!(document.querySelector('#summary').compareDocumentPosition(document.querySelector('nav'))&Node.DOCUMENT_POSITION_FOLLOWING),visibleHeaderText:document.querySelector('header').innerText,firstNumber:document.querySelector('#summary .number').getBoundingClientRect().toJSON()})''')
            first_use['contentsInitiallyOpen']=contents_details.evaluate('e=>e.open')
            check(not first_use['metadataInitiallyOpen'] and not first_use['contentsInitiallyOpen'],label+': first-use disclosures must start collapsed')
            check(first_use['summaryBeforeContents'],label+': contents precede achievements')
            check('ordinary RH' in first_use['visibleHeaderText'] and 'source proposition' in first_use['visibleHeaderText'],label+': visible source-assumption boundary missing')
            check(first_use['firstNumber']['top']>=0 and first_use['firstNumber']['bottom']<=vp['height']+1,label+': first achievement bound not fully visible on initial screen')
            fonts = actual_fonts(page)
            for row in fonts:
                if row['present']:
                    check(row['actual_platform_fonts'] and all('STIX' in f['familyName'] for f in row['actual_platform_fonts']),
                          label + ': actual Greek glyph font fallback ' + row['character'])
            check(any(x['present'] and x['character'] == 'π' for x in fonts), label + ': no actual pi glyph inspected')
            check(any(x['present'] and x['character'] in ['ϑ','θ'] for x in fonts), label + ': no actual theta glyph inspected')
            disclosures=[]
            for name,button,details in [('metadata',meta_summary,meta_details),('contents',contents_summary,contents_details)]:
                button.focus();page.keyboard.press('Enter');opened=details.evaluate('e=>e.open')
                check(opened,label+': native disclosure Enter failed '+name)
                if name=='metadata':check(metadata['source_revision'] in details.inner_text(),label+': displayed source revision differs from metadata')
                path=output/(label+'-'+name+'-open.png');page.screenshot(path=str(path));screenshots.append(path)
                button.focus();page.keyboard.press('Space');closed=not details.evaluate('e=>e.open')
                check(closed,label+': native disclosure Space failed '+name)
                disclosures.append(dict(name=name,actual_keyboard_Enter_open=opened,actual_keyboard_Space_close=closed))
            for key in ['target','schoenfeld','buthe','transport','bptsource','bwsource','zeroenv','lnsource','fkssource','lnimpact','lnrepair','huxleydensity','inghamsource','classicalcube','cube966','cubeearly','cubetrE','finiteexact','finitelog','duality','population2026','raw2026','explicitE','componentcost','signedmoment','refinedbudget','Efrontier','newEpop']:

                loc = page.locator('[data-formula="' + key + '"]')
                if loc.count():
                    path = output / (label + '-math-' + key + '.png')
                    loc.first.screenshot(path=str(path)); screenshots.append(path)
                    size=loc.first.evaluate('e=>({client:e.clientWidth,scroll:e.scrollWidth})')
                    if size['scroll']>size['client']+8:
                        loc.first.evaluate('e=>e.scrollLeft=e.scrollWidth')
                        right=loc.first.evaluate('e=>e.scrollLeft')
                        check(right>0,label+': critical formula cannot pan to its domain '+key)
                        path=output/(label+'-math-'+key+'-right.png')
                        loc.first.screenshot(path=str(path));screenshots.append(path)
                        loc.first.evaluate('e=>e.scrollLeft=0')
            for section in ['summary','trust','population-figure','competition','experiments','network','resources','sources']:
                loc = page.locator('#' + section)
                if loc.count():
                    loc.evaluate('e=>e.scrollIntoView({block:"start",behavior:"instant"})')
                    path = output / (label + '-section-' + section + '.png')
                    page.screenshot(path=str(path)); screenshots.append(path)
            page.goto(frozen.as_uri(), wait_until='load'); page.evaluate('document.fonts.ready')
            page.keyboard.press('Tab')
            focused = page.evaluate('document.activeElement.classList.contains("skip")')
            check(focused, label + ': first keyboard Tab misses skip link')
            path = output / (label + '-keyboard-skip.png'); page.screenshot(path=str(path)); screenshots.append(path)
            page.keyboard.press('Enter')
            check(urlsplit(page.url).fragment == 'summary', label + ': keyboard skip-link target failed')
            contents_summary,contents_details=native_disclosure(page,'Detailed contents and evidence')
            contents_summary.focus();page.keyboard.press('Enter')
            check(contents_details.evaluate('e=>e.open'),label+': contents not open for keyboard anchor traversal')
            anchors = page.locator('a[href^="#"]').evaluate_all('(xs)=>xs.map(x=>x.getAttribute("href"))')
            anchor_results = []
            for href in sorted(set(anchors)):
                identifier = href[1:]
                target = page.locator('[id="' + identifier + '"]')
                check(target.count() == 1, label + ': missing/duplicate anchor ' + href)
                if target.count() != 1: continue
                link = page.locator('a[href="' + href + '"]').first
                link.focus(); page.keyboard.press('Enter')
                box = target.bounding_box()
                visible = box is not None and box['y'] < vp['height'] and box['y'] + box['height'] > 0
                ok = urlsplit(page.url).fragment == identifier and visible
                check(ok, label + ': keyboard anchor failed ' + href)
                anchor_results.append(dict(href=href, pass_actual_keyboard_navigation=ok))
            scrolls = page.locator('.scroll,.formula').evaluate_all('''xs=>xs.map(x=>({kind:x.className,
                formula:x.dataset.formula||null,tabIndex:x.tabIndex,client:x.clientWidth,scroll:x.scrollWidth,
                left:x.getBoundingClientRect().left,right:x.getBoundingClientRect().right}))''')
            for row in scrolls:
                check(row['left'] >= -1 and row['right'] <= vp['width'] + 1, label + ': scroll-container boundary overflow')
                if row['scroll'] > row['client'] + 1: check(row['tabIndex'] >= 0, label + ': nonkeyboard scroll container')
            keyboard_scroll = []
            for selector in ['.scroll','.formula']:
                indices = page.locator(selector).evaluate_all('(xs)=>xs.map((x,i)=>x.scrollWidth>x.clientWidth+8?i:-1).filter(i=>i>=0)')
                if not indices: continue
                loc = page.locator(selector).nth(indices[0]); loc.focus(); loc.evaluate('e=>e.scrollLeft=0')
                before = loc.evaluate('e=>e.scrollLeft')
                for _ in range(6): page.keyboard.press('ArrowRight')
                page.wait_for_timeout(250)
                after = loc.evaluate('e=>e.scrollLeft')
                check(after > before, label + ': horizontal keyboard scrolling failed ' + selector)
                keyboard_scroll.append(dict(selector=selector, before=before, after=after))
            if not results: links = source_links(page, metadata, a.repository, a.verify_source_links)
            results.append(dict(viewport=vp, dimensions=dims, math_count=page.locator('math').count(),
                                prose_paragraphs=len(paragraphs), initial_summary_first_use=first_use, native_disclosure_keyboard=disclosures, header_source_pin_colors=header_colors, all_header_muted_colors=header_all_colors, actual_fonts=fonts, anchors=anchor_results, all_MathML_render_boxes=visible_math,
                                scroll_containers=scrolls, actual_keyboard_horizontal_scroll=keyboard_scroll,
                                source_and_browser_paragraphs_identical=paragraphs==parsed.paragraphs))
            context.close()
        browser.close()
    check(not errors, 'Actual browser page errors')
    check(not any(r['scheme'] in ['http','https'] for r in requests), 'Unexpected online asset request')
    check(sha(a.html) == original_sha, 'Original report changed during browser QA')
    check(sha(a.metadata_path) == a.metadata_sha, 'Report metadata changed during browser QA')
    check(sha(Path(__file__)) == a.controller_sha, 'Browser QA controller changed during execution')
    check(not any(r['scheme']=='file' and urlsplit(r['url']).path!=urlsplit(frozen.as_uri()).path for r in requests), 'Report requested a separate local asset')
    receipt = dict(status='PASS_ACTUAL_OFFLINE_BROWSER_QA' if not problems else 'FAIL_ACTUAL_BROWSER_QA',
                   acceptance_scope='Offline desktop/mobile/keyboard/MathML/font/prose/overflow; mathematical proof, source-audit completion, experiment outcomes and remote publication are separate gates.',
                   python_optimization=sys.flags.optimize, source_html_sha256=original_sha,
                   source_report_metadata=metadata, controller_sha256=a.controller_sha, seconds=time.monotonic()-a.started,
                   browser_sha256=sha(a.browser), browser_version=version, playwright='1.62.0',
                   source_link_gate=links, checks=results, problems=problems, page_errors=errors,
                   requests=requests, screenshots=[dict(path=p.name,sha256=sha(p),bytes=p.stat().st_size) for p in screenshots])
    atomic(output / ('RESULT.json' if not problems else 'FAILED.json'), receipt)
    need(not problems, '; '.join(problems))
    print(json.dumps(dict(status=receipt['status'],viewports=len(results),math_count=parsed.math,
                          screenshots=len(screenshots),optimization=sys.flags.optimize,
                          source_link_release_gate=a.verify_source_links)))

def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--html',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--metadata',type=Path);p.add_argument('--browser',type=Path,default=Path(BROWSER))
    p.add_argument('--viewports',default='1280x900,390x844,320x740');p.add_argument('--repository',type=Path)
    p.add_argument('--verify-source-links',action='store_true');a=p.parse_args()
    a.viewports=viewport_list(a.viewports);a.html=a.html.resolve(strict=True);a.browser=a.browser.resolve(strict=True)
    if a.repository is not None:a.repository=a.repository.resolve(strict=True)
    if a.verify_source_links:need(a.repository is not None,'Source-link gate requires --repository')
    need(not a.output.exists() and not os.path.lexists(a.output),'Fresh output directory required')
    a.metadata_path=(a.metadata or a.html.with_name('REPORT_BUILD.json')).resolve(strict=True)
    a.metadata_sha=sha(a.metadata_path);a.controller_sha=sha(Path(__file__));a.started=time.monotonic()
    metadata=read_json(a.metadata_path)
    need(isinstance(metadata,dict),'Report metadata is not an object')
    need(isinstance(metadata.get('html_sha256'),str) and re.fullmatch('[0-9a-f]{64}',metadata['html_sha256']) is not None,'Invalid HTML hash metadata')
    need(type(metadata.get('rendered_occurrences')) is int,'Invalid MathML population metadata')
    need(isinstance(metadata.get('source_revision'),str),'Invalid pinned source revision')
    original_sha=sha(a.html);need(metadata['html_sha256']==original_sha,'HTML metadata hash differs')
    text=a.html.read_text()
    fonts=re.findall(r'src:url\(data:font/ttf;base64,([A-Za-z0-9+/=]+)\)',text)
    need(len(fonts)==1,'Report must embed exactly one pinned math font')
    font_sha=hashlib.sha256(base64.b64decode(fonts[0],validate=True)).hexdigest()
    need(font_sha==metadata.get('math_font_sha256')=='167378031e2dddc6216d67819c9260e9a06ffc4c478e4e23cb98a6fd44b183c2','Embedded math font bytes differ')
    parsed=SourceHTML();parsed.feed(text);need(parsed.current is None,'Unclosed source paragraph')
    need(parsed.scripts==0,'Static report contains script');need(parsed.math>=20,'Insufficient MathML source population')
    need(parsed.math==metadata['rendered_occurrences'],'MathML metadata population differs')
    need(re.fullmatch('[0-9a-f]{40}',metadata['source_revision']) is not None,'Invalid pinned source revision')
    a.output.mkdir(parents=True);frozen=a.output/'source'/a.html.name;frozen.parent.mkdir();frozen.write_bytes(a.html.read_bytes())
    need(sha(frozen)==original_sha,'Source changed while freezing browser input')
    (frozen.parent/'check_report_browser.py').write_bytes(Path(__file__).read_bytes())
    need(sha(frozen.parent/'check_report_browser.py')==a.controller_sha,'Controller changed while freezing browser input')
    try:
        run(a,a.output,metadata,parsed,frozen,original_sha)
    except Exception as e:
        if not (a.output/'FAILED.json').exists():
            atomic(a.output/'FAILED.json',dict(status='FAIL_BROWSER_EXECUTION_NO_ACCEPTANCE',error=str(e),source_html_sha256=original_sha,controller_sha256=a.controller_sha))
        raise
if __name__=='__main__':main()
