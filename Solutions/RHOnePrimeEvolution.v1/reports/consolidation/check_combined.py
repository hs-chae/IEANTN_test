#!/usr/bin/env python3
"""Independent static and actual offline browser readback of the merged report."""
from collections import Counter
from html.parser import HTMLParser
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import re
import time
from urllib.parse import unquote, urlparse
from playwright.sync_api import sync_playwright


def need(value, message):
    if not value:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Document(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.sections = []
        self.paragraphs = []
        self.paragraph = None
        self.scope = ''
        self.skip_math = 0
        self.ids = []
        self.hrefs = []
        self.styles = 0

    def handle_starttag(self, tag, attrs):
        data = dict(attrs)
        if 'id' in data:
            self.ids.append(data['id'])
        if tag == 'a':
            self.hrefs.append(data.get('href', ''))
        if tag == 'style':
            self.styles += 1
        if tag == 'section':
            self.sections.append(data.get('id', ''))
        if tag == 'p' and self.sections:
            self.paragraph = []
            self.scope = self.sections[-1]
        if tag == 'math' and self.paragraph is not None:
            self.skip_math += 1

    def handle_data(self, value):
        if self.paragraph is not None and not self.skip_math:
            self.paragraph.append(value)

    def handle_endtag(self, tag):
        if tag == 'math' and self.paragraph is not None:
            self.skip_math -= 1
        if tag == 'p' and self.paragraph is not None:
            self.paragraphs.append((self.scope, ''.join(self.paragraph)))
            self.paragraph = None
        if tag == 'section':
            self.sections.pop()


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--report', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    repo = Path('/data/ivy-rh-one-prime-20261124/network')
    reports = repo / 'Solutions/RHOnePrimeEvolution.v1/reports'
    names = ['RH_PAPER_SUMMARY_EN.html', 'RH_ONE_PRIME_FRONTIER_EN.html', 'RH_NETWORK_EVOLUTION_EN.html']
    actual_path = args.report.resolve(strict=True)
    raw = actual_path.read_text()
    initial_hash = digest(actual_path)
    result = {'status': 'INCOMPLETE', 'report': str(actual_path), 'sha256': initial_hash}
    args.out.mkdir(parents=True, exist_ok=False)
    parsed = Document()
    parsed.feed(raw)
    need(parsed.styles == 1, 'Expected one shared style/font declaration')
    need(len(parsed.ids) == len(set(parsed.ids)), 'Duplicate IDs')
    need(all(h[1:] in parsed.ids for h in parsed.hrefs if h.startswith('#')), 'Broken internal anchor')
    expected_math = []
    expected_paragraphs = Counter()
    expected_external = set()
    verification = None
    inputs = []
    for name in names:
        path = reports / name
        source = path.read_text()
        input_parser = Document()
        input_parser.feed(source)
        expected_math += re.findall(r'<math\b.*?</math>', source, re.S)
        expected_external.update(h for h in input_parser.hrefs if h.startswith('https://'))
        for scope, prose in input_parser.paragraphs:
            if scope != 'verification':
                expected_paragraphs[prose] += 1
        v = [p for scope, p in input_parser.paragraphs if scope == 'verification']
        if v:
            if verification is None:
                verification = v
            else:
                need(v == verification, 'Source verification paragraphs were not duplicates')
        inputs.append({'path': str(path), 'sha256': digest(path),
                       'mathml': len(re.findall(r'<math\b', source)), 'paragraphs': len(input_parser.paragraphs)})
    expected_paragraphs.update(verification or [])
    actual_math = re.findall(r'<math\b.*?</math>', raw, re.S)
    need(actual_math == expected_math and len(actual_math) == 127, 'Exact ordered MathML preservation failed')
    actual_paragraphs = Counter(p for _, p in parsed.paragraphs)
    missing = expected_paragraphs - actual_paragraphs
    need(not missing, 'Original section prose missing: ' + str(list(missing)[:2]))
    need(expected_external <= set(parsed.hrefs), 'Original primary/source link omitted')
    need(not any(h.startswith('../') for h in parsed.hrefs), 'Attachment still depends on relative research links')
    result.update(inputs=inputs, exact_ordered_mathml=127,
                  preserved_section_paragraphs=sum(expected_paragraphs.values()),
                  duplicate_verification_paragraphs_removed=len(verification or []),
                  one_style_font=True, unique_ids=len(parsed.ids), original_external_urls_preserved=len(expected_external))
    spec = importlib.util.spec_from_file_location('original_browser_check', reports / 'check_report_browser.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    rows = []
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        result['browser_version'] = browser.version
        for width in (390, 1280):
            context = browser.new_context(viewport={'width': width, 'height': 1000},
                                          java_script_enabled=False, offline=True, reduced_motion='reduce')
            page = context.new_page()
            requests, errors = [], []
            page.on('request', lambda request: requests.append(request.url))
            page.on('pageerror', lambda error: errors.append(str(error)))
            page.goto(actual_path.as_uri(), wait_until='load')
            page.evaluate('document.fonts.ready')
            for item in page.locator('details').all():
                if not item.evaluate('(e)=>e.open'):
                    item.locator(':scope > summary').focus()
                    page.keyboard.press('Enter')
                    need(item.evaluate('(e)=>e.open'), 'Native detail could not open with keyboard')
            data = page.evaluate(checker.OBSERVE)
            need(not errors, 'Actual browser errors')
            need(data['language'] == 'en', 'Wrong language')
            need(data['documentWidth'] <= width + 1, 'Document phone/desktop overflow')
            need(data['scripts'] == 0 and not data['inlineEventHandlers'] and not data['javascriptLinks'], 'Runtime script detected')
            need(data['mathCount'] == 127 and data['invisibleMath'] == 0 and data['wrongMathNamespace'] == 0, 'Invisible/wrong static math')
            need(data['mathFontReady'] and not data['wrongMathFonts'], 'Actual STIX math font not loaded')
            need(not data['rawVisibleTex'] and not data['unintendedHtml'], 'Raw TeX or unintended HTML')
            need(not data['duplicateIds'] and not data['brokenAnchors'], 'DOM anchor/ID failure')
            need(not any(urlparse(x).scheme in ('http', 'https') for x in requests), 'External load in offline report')
            wide = [(i, d) for i, d in enumerate(data['horizontalContainers']) if d['scrollWidth'] > d['width'] + 2]
            need(all(d['focusable'] and d['overflow'] in ['auto', 'scroll'] for i, d in wide), 'Wide content cannot focus/scroll')
            keyboard_scrolled = []
            for selector in ['.formula', '.tablewrap']:
                for item in page.locator(selector).all():
                    if item.evaluate('(e)=>e.scrollWidth-e.clientWidth') <= 25:
                        continue
                    item.evaluate('(e)=>e.scrollLeft=0')
                    item.focus()
                    page.keyboard.press('ArrowRight')
                    limit = time.monotonic() + 2
                    while item.evaluate('(e)=>e.scrollLeft') <= 0 and time.monotonic() < limit:
                        page.wait_for_timeout(50)
                    need(item.evaluate('(e)=>e.scrollLeft') > 0, 'Actual keyboard horizontal scroll failed')
                    keyboard_scrolled.append(selector)
                    break
            if width == 390:
                need(set(keyboard_scrolled) == {'.formula', '.tablewrap'}, 'Phone math/table keyboard cases absent')
            navigation = page.locator('nav a[href^="#"]')
            need(navigation.count() >= 3, 'Combined chapter navigation absent')
            hashes = []
            for link in navigation.all():
                href = link.get_attribute('href')
                link.focus()
                need(link.evaluate('(e)=>getComputedStyle(e).outlineStyle!=="none"'), 'Focused nav lacks visible outline')
                page.keyboard.press('Enter')
                need(page.evaluate('location.hash') == href, 'Actual nav activation failed')
                hashes.append(href)
            card = page.locator('#frontier-lee')
            need(card.count() == 1, 'Lee source comparison card absent')
            critical_style = card.evaluate('(e)=>({width:getComputedStyle(e).borderLeftWidth,color:getComputedStyle(e).borderLeftColor})')
            need(critical_style == {'width': '5px', 'color': 'rgb(164, 61, 56)'}, 'Critical source card lost red border')
            for href in parsed.hrefs:
                u = urlparse(href)
                if u.netloc == 'github.com' and '/IEANTN_test/blob/' in u.path:
                    m = re.fullmatch(r'/hs-chae/IEANTN_test/blob/([0-9a-f]{40})/(.+)', u.path)
                    need(m and m[1] in ['109729571ac5e6ea38944c965abad11a8dad4d43', '86b232f17321b77cdbd7f63b4febb020a81560b9'], 'Unexpected source revision')
                    target = repo / unquote(m[2])
                    need(target.is_file() and not target.is_symlink(), 'Actual source link missing')
            page.evaluate('scrollTo({top:0,behavior:"instant"})')
            shot = args.out / ('combined-' + str(width) + '-top.png')
            page.screenshot(path=str(shot))
            rows.append({'width': width, 'document_width': data['documentWidth'], 'visible_mathml': data['mathCount'],
                         'keyboard_scrolled_types': keyboard_scrolled, 'wide_containers_checked': len(wide),
                         'keyboard_navigation': hashes, 'critical_card_style': critical_style,
                         'external_requests': 0, 'javascript_enabled': False, 'offline': True,
                         'screenshot': str(shot), 'screenshot_sha256': digest(shot)})
            context.close()
        browser.close()
    need(digest(actual_path) == initial_hash, 'Report changed while checked')
    result.update(status='PASS_EXACT_MATH_PROSE_SOURCE_LINKS_AND_ACTUAL_OFFLINE_PHONE_DESKTOP', browser_cases=rows,
                  checker_sha256=digest(Path(__file__)))
    (args.out / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'mathml': 127, 'paragraphs': sum(expected_paragraphs.values()),
                      'browser_cases': len(rows), 'sha256': initial_hash}))


if __name__ == '__main__':
    main()
