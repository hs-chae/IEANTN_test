"""Check the actual capped-session HTML offline; this is not proof acceptance."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
from urllib.parse import unquote, urlsplit
from playwright.sync_api import sync_playwright

B = Path(__file__).resolve().parent
R = B.parents[1]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--report', type=Path, required=True)
    ap.add_argument('--sha256', required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    report, out = args.report.resolve(), args.out.resolve()
    need(report.is_relative_to(R) and sha(report) == args.sha256, 'exact frozen report')
    need(out.is_relative_to(B) and not out.exists(), 'fresh owned browser output')
    out.mkdir(parents=True)
    rows = []
    with sync_playwright() as runner:
        browser = runner.chromium.launch(headless=True)
        for width in [390, 1440]:
            page = browser.new_page(viewport={'width': width, 'height': 950})
            errors, external = [], []
            page.on('pageerror', lambda error: errors.append(str(error)))

            def route(request):
                if request.request.url.startswith('file:'):
                    request.continue_()
                else:
                    external.append(request.request.url)
                    request.abort()

            page.route('**/*', route)
            page.goto(report.as_uri(), wait_until='load')
            page.evaluate('document.fonts.ready')
            row = page.evaluate(r'''()=>{
              const raw=[];const w=document.createTreeWalker(document.body,NodeFilter.SHOW_TEXT);
              let n;while(n=w.nextNode())if(!n.parentElement.closest('math,style,script,code')&&/\^|<=|>=|\\\(|\\\[|\$[^$]+\$/.test(n.textContent))raw.push(n.textContent.trim());
              const panels=[...document.querySelectorAll('.scroll,.formula')].filter(e=>e.scrollWidth>e.clientWidth+1);
              return {width:innerWidth,documentWidth:document.documentElement.scrollWidth,
                mathCount:document.querySelectorAll('math').length,scripts:document.scripts.length,
                badMath:[...document.querySelectorAll('mfrac,msub,msup,mroot,mover,munder')].filter(e=>e.children.length!==2).length,
                badAnchors:[...document.querySelectorAll('a[href^="#"]')].filter(e=>!document.getElementById(e.hash.slice(1))).length,
                hrefs:[...document.querySelectorAll('a')].map(e=>e.getAttribute('href')),
                rawFormulaText:raw,
                inaccessible:panels.filter(e=>getComputedStyle(e).overflowX!=='auto'||e.tabIndex!==0).length,
                stoppedStatement:document.body.innerText.includes('All session jobs have stopped.'),
                tables:document.querySelectorAll('table').length,
                mathFont:getComputedStyle(document.querySelector('math')).fontFamily,
                fontReady:document.fonts.status==='loaded'};
            }''')
            local = []
            for href in row['hrefs']:
                link = urlsplit(href)
                if not link.scheme and link.path:
                    path = (report.parent/unquote(link.path)).resolve()
                    need(path.is_relative_to(R) and path.is_file(), 'working actual local download target')
                    local.append({'href': href, 'sha256': sha(path), 'bytes': path.stat().st_size})
                elif link.netloc == 'raw.githubusercontent.com':
                    parts = unquote(link.path).strip('/').split('/')
                    need(link.scheme == 'https' and parts[:2] == ['hs-chae', 'IEANTN_test']
                         and len(parts) > 3 and re.fullmatch('[0-9a-f]{40}', parts[2]),
                         'pinned public artifact URL')
                    path = (R/'network'/Path(*parts[3:])).resolve()
                    need(path.is_relative_to(R/'network') and path.is_file(),
                         'actual local counterpart of each immutable download link')
                    local.append({'href': href, 'sha256': sha(path), 'bytes': path.stat().st_size,
                                  'qualification': 'Local artifact counterpart; actual HTTP byte verification follows publication.'})
            row['local_downloads'] = local
            page.keyboard.press('Tab')
            row['keyboard_first_focus'] = page.evaluate('document.activeElement.tagName')
            page.screenshot(path=str(out/f'{width}-top.png'), full_page=False)
            page.locator('nav a[href="#reproduce"]').click()
            row['navigation_target'] = page.evaluate('location.hash')
            page.screenshot(path=str(out/f'{width}-reproduce.png'), full_page=False)
            row.update(errors=errors, external_requests=external)
            rows.append(row)
            (out/'PARTIAL.json').write_text(json.dumps(rows, indent=2)+'\n')
            need(row['documentWidth'] <= width and row['mathCount'] == 3
                 and row['tables'] == 4 and not row['scripts'] and not row['badMath']
                 and not row['badAnchors'] and not row['rawFormulaText'] and not row['inaccessible']
                 and row['stoppedStatement'] and row['fontReady'] and not errors and not external
                 and row['keyboard_first_focus'] not in ['HTML', 'BODY']
                 and row['navigation_target'] == '#reproduce', 'offline/mobile/keyboard/static-math gate')
            page.close()
        browser.close()
    need(sha(report) == args.sha256, 'report stayed frozen during browser checks')
    receipt = {'status': 'PASS_ACTUAL_CAPPED_REPORT_OFFLINE_BROWSER',
               'report_sha256': args.sha256, 'checker_sha256': sha(Path(__file__)),
               'rows': rows,
               'qualification': 'Readability/download-link evidence only, not a mathematical or source-first verification verdict.'}
    pending = out/'RECEIPT.json.pending'
    pending.write_text(json.dumps(receipt, indent=2, allow_nan=False)+'\n')
    os.replace(pending, out/'RECEIPT.json')
    print(receipt['status'])


if __name__ == '__main__':
    main()
