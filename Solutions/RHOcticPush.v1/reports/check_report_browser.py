#!/usr/bin/env python3
"""Inspect the actual offline reports at phone and desktop widths.

This is document verification, not mathematical theorem or PV acceptance.
The source-link check is local; final remote Git blob checks are separate.
"""
import argparse
import hashlib
import json
import re
from importlib.metadata import version
from pathlib import Path
from urllib.parse import unquote, urlparse
from playwright.sync_api import sync_playwright


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--reports', type=Path, required=True)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    source, repo, out = args.reports.resolve(), args.repo.resolve(), args.out.resolve()
    require(not out.exists() and out.parent.is_dir(), 'Use a fresh owned output directory')
    reports = [(lang, source/('RH_OCTIC_RESEARCH_'+lang+'.html')) for lang in ['EN', 'KO']]
    reports.append(('PAPER_EN', source/'RH_OCTIC_PAPER_EN.html'))
    require(all(path.is_file() for _, path in reports), 'Both complete reports and paper required')
    out.mkdir()
    rows = []
    with sync_playwright() as playwright:
        browser = playwright.chromium.launch(headless=True)
        browser_version = browser.version
        for language, report in reports:
            for width in [390, 1280]:
                context = browser.new_context(viewport={'width': width, 'height': 1000})
                page = context.new_page()
                requests, errors = [], []
                page.on('request', lambda request: requests.append(request.url))
                page.on('pageerror', lambda error: errors.append(str(error)))
                page.goto(report.as_uri(), wait_until='load')
                page.evaluate('document.fonts.ready')
                data = page.evaluate('''() => {
                  const all = s => Array.from(document.querySelectorAll(s));
                  const ids = all('[id]').map(e => e.id);
                  const intendedHtml = new Set(['html','head','meta','title','style','body',
                    'main','p','h1','h2','h3','h4','nav','a','section','article','div','span',
                    'strong','em','b','code','pre','details','summary','ul','ol','li',
                    'table','thead','tbody','tr','th','td','footer','br','hr']);
                  return {
                    language: document.documentElement.lang,
                    width: innerWidth, documentWidth: document.documentElement.scrollWidth,
                    scripts: all('script').length,
                    mathCount: all('math').length,
                    invisibleMath: all('math').filter(e => {
                      const r=e.getBoundingClientRect(); return r.width<=0 || r.height<=0;
                    }).length,
                    mathFontReady: document.fonts.check('16px ReportSTIX', 'πγρδψθ'),
                    rawVisibleTex: /\\\\(?:frac|sqrt|begin|operatorname)|\\$\\$/.test(document.body.innerText),
                    duplicateIds: ids.filter((id,i) => ids.indexOf(id)!==i),
                    unintendedHtml: all('*').filter(e =>
                      e.namespaceURI==='http://www.w3.org/1999/xhtml' &&
                      !intendedHtml.has(e.localName)).map(e => e.localName),
                    brokenAnchors: all('a[href^="#"]').map(e => e.getAttribute('href'))
                      .filter(h => !document.getElementById(decodeURIComponent(h.slice(1)))),
                    hrefs: all('a[href]').map(e => e.getAttribute('href')),
                    horizontalContainers: all('.formula,.tablewrap').filter(e =>
                      e.scrollWidth>e.clientWidth+2).map(e => ({
                        overflow: getComputedStyle(e).overflowX,
                        focusable: e.getAttribute('tabindex')==='0'
                      })),
                    sections: all('main section').map(e => e.id)
                  };
                }''')
                (out/(language+'-'+str(width)+'-observations.json')).write_text(
                    json.dumps(data, indent=2)+'\n')
                require(not errors, 'Browser runtime errors')
                require(data['scripts'] == 0, 'Offline reports must not execute scripts')
                require(data['documentWidth'] <= width+1, 'Document escapes phone/desktop viewport')
                require(data['mathCount'] > 70 and data['invisibleMath'] == 0,
                        'Every static formula must render visibly')
                require(data['mathFontReady'], 'Embedded Greek/math font unavailable')
                require(not data['rawVisibleTex'], 'Unrendered visible TeX')
                require(not data['duplicateIds'] and not data['brokenAnchors'],
                        'Duplicate IDs or broken internal navigation')
                require(not data['unintendedHtml'],
                        'Unexpected HTML elements; a prose inequality may have been parsed as markup')
                require(all(item['overflow'] in ['auto', 'scroll'] and item['focusable']
                            for item in data['horizontalContainers']),
                        'Wide formulas/tables need visible and keyboard-usable horizontal scrolling')
                require(not any(urlparse(url).scheme in ['http', 'https'] for url in requests),
                        'External requests required to read supposedly offline report')
                wide = page.locator('.formula,.tablewrap').filter(has=page.locator('math,table,svg'))
                keyboard_scroll = False
                for index in range(wide.count()):
                    item = wide.nth(index)
                    if item.evaluate('(e) => e.scrollWidth>e.clientWidth+25'):
                        item.focus()
                        page.keyboard.press('ArrowRight')
                        page.wait_for_timeout(180)
                        require(item.evaluate('(e) => e.scrollLeft>0'),
                                'Focused wide formula/table does not scroll with arrow keys')
                        item.evaluate('(e) => e.scrollLeft=0')
                        keyboard_scroll = True
                        break
                require(keyboard_scroll, 'No actual keyboard horizontal-scroll check')
                page.evaluate('scrollTo(0,0)')
                links = []
                for href in data.pop('hrefs'):
                    parsed = urlparse(href)
                    if parsed.netloc == 'github.com' and '/IEANTN_test/blob/' in parsed.path:
                        suffix = parsed.path.split('/IEANTN_test/blob/', 1)[1]
                        # The historical draft uses a slash-containing branch;
                        # final reports use an exact40hex source commit.
                        if suffix.startswith('research/rh-octic-full-network-20261123/'):
                            relative = suffix[len('research/rh-octic-full-network-20261123/'):]
                        else:
                            revision, relative = suffix.split('/', 1)
                            require(re.fullmatch('[0-9a-f]{40}', revision) is not None,
                                    'Unexpected source revision in report link')
                        relative = unquote(relative)
                        target = (repo/relative).resolve()
                        require(target.is_relative_to(repo) and target.is_file(),
                                'Absent linked actual source file: '+relative)
                        links.append({'path': relative, 'sha256': sha(target)})
                page.screenshot(path=str(out/(language+'-'+str(width)+'-top.png')))
                feedback = page.locator('#feedback')
                feedback.scroll_into_view_if_needed()
                page.screenshot(path=str(out/(language+'-'+str(width)+'-feedback.png')))
                # Exercise keyboard navigation independently of pointer scrolling.
                if language != 'PAPER_EN':
                    focus = page.locator('nav a').first
                    focus.focus()
                    require(focus.evaluate('(e) => e===document.activeElement'),
                            'Navigation cannot receive keyboard focus')
                    page.keyboard.press('Enter')
                    require(page.evaluate('location.hash') != '', 'Keyboard anchor did not navigate')
                rows.append({'report': report.name, 'sha256': sha(report), 'width': width,
                             'observed': data, 'linked_local_sources': links,
                             'external_network_requests': [], 'page_errors': errors})
                context.close()
        browser.close()
    receipt = {'status': 'PASS_ACTUAL_OFFLINE_REPORT_BROWSER_AND_LOCAL_LINK_CHECKS',
               'scope': 'Document rendering/navigation/local source identity only; '
                        'independent mathematics and final remote-publication checks remain separate.',
               'playwright_version': version('playwright'), 'browser_version': browser_version,
               'rows': rows}
    (out/'RESULT.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(receipt['status'], 'phone/desktop cases', len(rows))


if __name__ == '__main__':
    main()
