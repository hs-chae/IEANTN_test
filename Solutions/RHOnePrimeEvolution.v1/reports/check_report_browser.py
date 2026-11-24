#!/usr/bin/env python3
"""Check all five actual offline reports with JavaScript disabled.

This checks rendering, complete prose preservation, navigation and local source
links. It is not mathematical acceptance, remote-publication validation or PV.
"""
import argparse
import base64
import hashlib
from importlib.metadata import version
import json
import os
from pathlib import Path
import re
import sys
import time
from urllib.parse import unquote, urlparse

from playwright.sync_api import sync_playwright


EXPECTED = {
    'RH_ONE_PRIME_FRONTIER_EN.html': ('en', 52),
    'RH_ONE_PRIME_FRONTIER_KO.html': ('ko', 52),
    'RH_NETWORK_EVOLUTION_EN.html': ('en', 67),
    'RH_NETWORK_EVOLUTION_KO.html': ('ko', 67),
    'RH_PAPER_SUMMARY_EN.html': ('en', 8),
}


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strict_json(text):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate JSON key '+key)
            result[key] = value
        return result
    return json.loads(text, object_pairs_hook=pairs)


def atomic(path, value):
    temporary = path.with_name(path.name+'.new')
    with temporary.open('x', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2, ensure_ascii=False)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def linked_files(hrefs, repo, report, revision):
    rows, remote = [], []
    prefix = '/hs-chae/IEANTN_test/blob/'+revision+'/'
    for href in sorted(set(hrefs)):
        parsed = urlparse(href)
        if href.startswith('#'):
            continue
        relative = None
        if parsed.netloc == 'github.com' and '/IEANTN_test/blob/' in parsed.path:
            require(parsed.path.startswith(prefix), 'Unexpected source revision in '+href)
            relative = unquote(parsed.path[len(prefix):])
            target = (repo/relative).resolve()
        elif not parsed.scheme and not parsed.netloc:
            target = (report.parent/unquote(parsed.path)).resolve()
            relative = str(target.relative_to(repo)) if target.is_relative_to(repo) else None
        else:
            remote.append(href)
            continue
        require(relative is not None and target.is_relative_to(repo) and target.is_file()
                and not target.is_symlink(), 'Absent actual linked local source: '+href)
        if parsed.fragment:
            match = re.fullmatch(r'L([0-9]+)(?:-L([0-9]+))?', parsed.fragment)
            if match:
                count = len(target.read_bytes().splitlines())
                require(1 <= int(match[1]) <= int(match[2] or match[1]) <= count,
                        'Source line fragment exceeds actual file: '+href)
        rows.append({'href': href, 'path': relative, 'sha256': sha(target)})
    return rows, remote


OBSERVE = r'''() => {
  const all = s => Array.from(document.querySelectorAll(s));
  const ids = all('[id]').map(e => e.id);
  const intended = new Set(['html','head','meta','title','style','body','main',
    'header','footer','nav','section','article','p','h1','h2','h3','h4','a','div',
    'span','strong','em','b','i','code','pre','details','summary','ul','ol','li',
    'table','thead','tbody','tr','th','td','dl','dt','dd','br','hr','sup','sub']);
  const main = document.querySelector('main').cloneNode(true);
  main.querySelectorAll('header,footer,math,style,script').forEach(e => e.remove());
  return {
    language: document.documentElement.lang,
    width: innerWidth, documentWidth: document.documentElement.scrollWidth,
    scripts: all('script').length,
    inlineEventHandlers: all('*').flatMap(e => Array.from(e.attributes))
      .filter(a => /^on/i.test(a.name)).map(a => a.name),
    mathCount: all('math').length,
    invisibleMath: all('math').filter(e => {
      const r=e.getBoundingClientRect(), s=getComputedStyle(e);
      return r.width<=0 || r.height<=0 || s.visibility==='hidden' || s.display==='none'
        || !e.checkVisibility();
    }).length,
    wrongMathNamespace: all('math').filter(e =>
      e.namespaceURI!=='http://www.w3.org/1998/Math/MathML').length,
    mathFontReady: document.fonts.check('16px STIX', 'πγρδψθ∑∫'),
    fontFaces: Array.from(document.fonts).map(f => ({family:f.family,status:f.status})),
    wrongMathFonts: all('math').map(e => getComputedStyle(e).fontFamily)
      .filter(f => !f.includes('STIX')),
    rawVisibleTex: /\\(?:frac|sqrt|begin|operatorname)|\$\$|\\\[|\\\(/.test(document.body.innerText),
    duplicateIds: ids.filter((id,i) => ids.indexOf(id)!==i),
    unintendedHtml: all('*').filter(e =>
      e.namespaceURI==='http://www.w3.org/1999/xhtml' && !intended.has(e.localName))
      .map(e => e.localName),
    brokenAnchors: all('a[href^="#"]').map(e => e.getAttribute('href'))
      .filter(h => h.length<2 || !document.getElementById(decodeURIComponent(h.slice(1)))),
    hrefs: all('a[href]').map(e => e.getAttribute('href')),
    javascriptLinks: all('a[href]').map(e => e.getAttribute('href'))
      .filter(h => /^javascript:/i.test(h)),
    horizontalContainers: all('.formula,.tablewrap').map(e => ({
      overflow: getComputedStyle(e).overflowX,
      focusable: e.getAttribute('tabindex')==='0',
      width:e.clientWidth,scrollWidth:e.scrollWidth,
      formula:e.getAttribute('data-formula')
    })),
    proseText: main.textContent,
    sections: all('main section').map(e => e.id)
  };
}'''


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument('--reports', type=Path, required=True)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    reports, repo, out = args.reports.resolve(strict=True), args.repo.resolve(strict=True), args.out.resolve()
    require(not out.exists() and out.parent.is_dir(), 'Fresh owned output directory required')
    build_path = reports/'REPORT_BUILD.json'
    initial_build_hash = sha(build_path)
    build = strict_json(build_path.read_text())
    table = {}
    for row in build['reports']:
        require(row['path'] not in table, 'Duplicate report identity')
        table[row['path']] = row
    require(set(table) == set(EXPECTED), 'Exact five requested reports required')
    require(set(p.name for p in reports.glob('*.html')) == set(EXPECTED),
            'Unaccounted HTML report')
    revision = build['source_revision']
    require(re.fullmatch(r'[0-9a-f]{40}', revision) is not None
            or revision == 'research/rh-one-prime-network-20261124', 'Unexpected source revision')
    font_hash = sha(reports/'fonts/STIXGeneral.ttf')
    for name, (_, count) in EXPECTED.items():
        report = reports/name
        require(sha(report) == table[name]['sha256'], 'Report/build hash mismatch '+name)
        require(table[name]['math_occurrences'] == count, 'Unexpected formula count '+name)
        require(hashlib.sha256(table[name]['prose_text'].encode()).hexdigest()
                == table[name]['prose_sha256'], 'Build prose identity mismatch '+name)
        embedded = re.findall(r'url\(data:font/ttf;base64,([A-Za-z0-9+/=]+)\)', report.read_text())
        require(len(embedded) == 1, 'Exactly one embedded STIX face required '+name)
        require(hashlib.sha256(base64.b64decode(embedded[0], validate=True)).hexdigest() == font_hash,
                'Embedded STIX payload differs from delivered font '+name)
    out.mkdir()
    rows, failures, all_source_paths = [], [], set()
    with sync_playwright() as playwright:
        browser = playwright.chromium.launch(headless=True)
        browser_version = browser.version
        for name, (language, math_count) in EXPECTED.items():
            report = reports/name
            for width in [390, 1280]:
                tag = report.stem+'-'+str(width)
                context = browser.new_context(viewport={'width': width, 'height': 1000},
                                              java_script_enabled=False, offline=True,
                                              reduced_motion='reduce')
                page = context.new_page()
                requests, errors = [], []
                page.on('request', lambda request: requests.append(request.url))
                page.on('pageerror', lambda error: errors.append(str(error)))
                observations = {'report': name, 'width': width}
                try:
                    page.goto(report.as_uri(), wait_until='load')
                    page.evaluate('document.fonts.ready')
                    # Native disclosures work without JavaScript. Exercise their
                    # actual keyboard control before checking all contained math.
                    disclosures = []
                    details = page.locator('details')
                    for index in range(details.count()):
                        item = details.nth(index)
                        initially_open = item.evaluate('(e) => e.open')
                        summary = item.locator(':scope > summary')
                        require(summary.count() == 1, tag+': disclosure needs one summary')
                        if not initially_open:
                            summary.focus()
                            require(summary.evaluate('(e) => e===document.activeElement'),
                                    tag+': disclosure summary cannot receive keyboard focus')
                            page.keyboard.press('Enter')
                            require(item.evaluate('(e) => e.open'),
                                    tag+': Enter failed to open disclosure')
                        disclosures.append({'summary': summary.inner_text(),
                                            'initially_open': initially_open,
                                            'opened_with_keyboard': not initially_open})
                    observations['native_disclosures'] = disclosures
                    page.evaluate('document.fonts.ready')
                    data = page.evaluate(OBSERVE)
                    observations['observed'] = data
                    observations['requests'] = requests
                    observations['page_errors'] = errors
                    require(not errors, tag+': browser error')
                    require(data['language'] == language, tag+': wrong language')
                    require(data['scripts'] == 0 and not data['inlineEventHandlers']
                            and not data['javascriptLinks'], tag+': runtime JavaScript')
                    require(data['documentWidth'] <= width+1, tag+': viewport overflow')
                    require(data['mathCount'] == math_count and data['invisibleMath'] == 0
                            and data['wrongMathNamespace'] == 0, tag+': invisible/missing static MathML')
                    require(data['mathFontReady'] and not data['wrongMathFonts']
                            and any(f['family'] == 'STIX' and f['status'] == 'loaded'
                                    for f in data['fontFaces']), tag+': STIX not actually loaded')
                    require(not data['rawVisibleTex'], tag+': raw TeX visible')
                    require(not data['duplicateIds'] and not data['brokenAnchors'], tag+': broken anchors/IDs')
                    require(not data['unintendedHtml'], tag+': unintended HTML: '+str(data['unintendedHtml']))
                    require(data['proseText'] == table[name]['prose_text'], tag+': complete body prose changed in DOM')
                    require(not any(urlparse(url).scheme in ['http', 'https'] for url in requests),
                            tag+': external request in offline document')
                    local, remote = linked_files(data['hrefs'], repo, report, revision)
                    observations['linked_local_sources'] = local
                    observations['primary_links_not_fetched_offline'] = remote
                    all_source_paths.update(row['path'] for row in local)
                    containers = data['horizontalContainers']
                    require(all(item['overflow'] in ['auto', 'scroll'] and item['focusable']
                                for item in containers if item['scrollWidth'] > item['width']+2),
                            tag+': wide formulas need keyboard focus and scrolling')
                    keyboard = []
                    observations['keyboard_horizontal_scroll'] = keyboard
                    for index, item in enumerate(containers):
                        if item['scrollWidth'] <= item['width']+25:
                            continue
                        locator = page.locator('.formula,.tablewrap').nth(index)
                        locator.evaluate('(e) => e.scrollIntoView({block:"center",inline:"nearest",behavior:"instant"})')
                        locator.evaluate('(e) => e.scrollLeft=0')
                        locator.focus()
                        require(locator.evaluate('(e) => e===document.activeElement'),
                                tag+': wide formula cannot focus')
                        attempt = {'formula': item['formula'], 'initial_scrollLeft':
                                   locator.evaluate('(e) => e.scrollLeft')}
                        keyboard.append(attempt)
                        require(attempt['initial_scrollLeft'] == 0,
                                tag+': wide formula did not reset for keyboard test')
                        page.keyboard.press('ArrowRight')
                        deadline = time.monotonic()+2
                        while locator.evaluate('(e) => e.scrollLeft') <= 0 and time.monotonic() < deadline:
                            page.wait_for_timeout(50)
                        offset = locator.evaluate('(e) => e.scrollLeft')
                        require(offset > 0, tag+': ArrowRight failed within2s for '+str(item['formula']))
                        attempt['arrow_scrollLeft'] = offset
                        locator.evaluate('(e) => e.scrollLeft=0')
                    if width == 390:
                        require(keyboard, tag+': no actual phone horizontal-scroll test')
                    navigation = page.locator('nav a')
                    require(navigation.count() >= 1, tag+': section navigation missing')
                    first = navigation.first
                    first.focus()
                    page.keyboard.press('Tab')
                    active = page.evaluate('document.activeElement.tagName')
                    require(active == 'A' or page.evaluate('document.activeElement.classList.contains("formula")'),
                            tag+': Tab did not reach another interactive element')
                    first.focus()
                    require(first.evaluate('(e) => getComputedStyle(e).outlineStyle!=="none"'),
                            tag+': focused navigation has no visible focus state')
                    anchor_checks = []
                    for index in range(navigation.count()):
                        link = navigation.nth(index)
                        href = link.get_attribute('href')
                        link.focus()
                        page.keyboard.press('Enter')
                        require(page.evaluate('location.hash') == href, tag+': Enter did not activate '+str(href))
                        anchor_checks.append(href)
                    observations['keyboard_anchor_checks'] = anchor_checks
                    page.evaluate('scrollTo({top:0,behavior:"instant"})')
                    page.wait_for_timeout(200)
                    page.screenshot(path=str(out/(tag+'-top.png')))
                    last_section = page.locator('main section').last
                    last_section.evaluate('(e) => e.scrollIntoView({block:"start",behavior:"instant"})')
                    page.screenshot(path=str(out/(tag+'-last-section.png')))
                    observations['status'] = 'PASS'
                    rows.append({'report': name, 'sha256': table[name]['sha256'], 'width': width,
                                 'observation_sha256_pending': tag+'.json'})
                    print('PASS '+tag, flush=True)
                except Exception as error:
                    observations['status'] = 'FAIL'
                    observations['error'] = str(error)
                    failures.append({'case': tag, 'error': str(error)})
                    page.screenshot(path=str(out/(tag+'-failure.png')))
                    print('FAIL '+tag+': '+str(error), flush=True)
                finally:
                    atomic(out/(tag+'.json'), observations)
                    context.close()
        browser.close()
    atomic(out/'OBSERVATIONS.json', {'rows': rows, 'failures': failures})
    require(not failures, 'Report browser failures: '+json.dumps(failures, ensure_ascii=False))
    atomic(out/'FINAL_GATES.json', {
        'browser_actual_source_paths': sorted(all_source_paths),
        'build_declared_source_paths': sorted(build['actual_repository_links']),
        'actual_paths_absent_from_build': sorted(all_source_paths-set(build['actual_repository_links'])),
        'build_paths_absent_from_dom': sorted(set(build['actual_repository_links'])-all_source_paths),
        'build_unchanged': sha(build_path) == initial_build_hash,
        'reports_unchanged': all(sha(reports/name) == table[name]['sha256'] for name in EXPECTED),
    })
    require(all_source_paths == set(build['actual_repository_links']),
            'Browser local-link universe differs from report build inventory')
    require(sha(build_path) == initial_build_hash, 'Build manifest changed during browser checks')
    for row in rows:
        require(sha(reports/row['report']) == row['sha256'], 'Report changed during browser checks')
        row['observation_sha256'] = sha(out/row.pop('observation_sha256_pending'))
    receipt = {'status': 'PASS_FIVE_OFFLINE_REPORTS_PHONE_DESKTOP_STATIC_MATH_PROSE_KEYBOARD_LOCAL_LINKS',
               'scope': 'Actual document/UI/local source checks only; mathematics, full proof replay and remote publication are separate.',
               'java_script_enabled': False, 'browser_offline': True,
               'browser_version': browser_version, 'playwright_version': version('playwright'),
               'checker_sha256': sha(Path(__file__).resolve()),
               'command': [sys.executable, *sys.argv], 'source_revision': revision,
               'report_build_sha256': sha(build_path), 'embedded_font_sha256': font_hash,
               'case_count': len(rows), 'unique_linked_local_sources': len(all_source_paths),
               'rows': rows, 'screenshots': {p.name: sha(p) for p in sorted(out.glob('*.png'))}}
    atomic(out/'RESULT.json', receipt)
    print(receipt['status']+' '+str(len(rows)))


if __name__ == '__main__':
    main()
