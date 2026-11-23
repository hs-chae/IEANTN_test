#!/usr/bin/env python3
"""Check the standalone scoped review HTML offline at desktop and phone widths."""
from pathlib import Path
import argparse, hashlib, json, os, re, urllib.parse
from playwright.sync_api import sync_playwright


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--out', required=True, type=Path)
    a = p.parse_args()
    source = Path(__file__).with_name('REVIEW.html')
    initial = sha(source)
    need(not a.out.exists(), 'fresh output required')
    for url in re.findall(r'href="([^"]+)"', source.read_text()):
        parsed = urllib.parse.urlparse(url)
        if not parsed.scheme:
            need((source.parent / urllib.parse.unquote(parsed.path)).exists(), 'broken local link: ' + url)
    a.out.mkdir(parents=True)
    rows, network = [], []
    with sync_playwright() as pw:
        browser = pw.chromium.launch(headless=True)
        for width in [1280, 390]:
            context = browser.new_context(viewport={'width': width, 'height': 900}, offline=True)
            context.on('request', lambda q: network.append(q.url) if q.url.startswith(('https://', 'http://')) else None)
            page = context.new_page()
            page.goto(source.resolve().as_uri())
            state = page.evaluate('''()=>({viewport:innerWidth,width:document.documentElement.scrollWidth,
                scripts:document.scripts.length,mathBlocks:document.querySelectorAll('.math').length,
                rawTex:document.body.innerText.includes(String.fromCharCode(92)+'(')||document.body.innerText.includes(String.fromCharCode(92)+'[')})''')
            need(state['width'] <= width and state['scripts'] == 0 and not state['rawTex'], 'offline readable layout')
            page.keyboard.press('Tab')
            focused = page.evaluate('''()=>({tag:document.activeElement.tagName,outline:getComputedStyle(document.activeElement).outlineStyle})''')
            need(focused['tag'] == 'A' and focused['outline'] != 'none', 'visible source-link keyboard focus')
            page.screenshot(path=str(a.out / (str(width) + '.png')))
            rows.append(dict(state, focus=focused))
            context.close()
        version = browser.version
        browser.close()
    need(not network and initial == sha(source), 'network use or input drift')
    result = {'status': 'PASS_SCOPED_REVIEW_HTML_OFFLINE_DESKTOP_AND390',
              'input_sha256': initial, 'checker_sha256': sha(__file__),
              'chromium_version': version, 'rows': rows, 'network_requests': network}
    pending = a.out / '.RESULT.pending'
    pending.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(pending, a.out / 'RESULT.json')
    print(result['status'])


if __name__ == '__main__':
    main()
