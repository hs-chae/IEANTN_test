#!/usr/bin/env python3
"""Inspect actual standalone MathML in desktop/mobile Chromium, without network."""
from pathlib import Path
import argparse
import hashlib
import importlib.metadata
import json
from playwright.sync_api import sync_playwright


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--html", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    need(not args.out.exists(), "fresh browser evidence directory required")
    report = args.html.resolve()
    identity = sha(report)
    args.out.mkdir(parents=True)
    records = []
    with sync_playwright() as api:
        executable = Path(api.chromium.executable_path)
        browser = api.chromium.launch(headless=True)
        for width, name in [(390, "mobile"), (1280, "desktop")]:
            page = browser.new_page(viewport={"width": width, "height": 900}, device_scale_factor=1)
            errors, network = [], []
            page.on("pageerror", lambda error: errors.append(str(error)))
            page.on("request", lambda request: network.append(request.url) if request.url.startswith(("http:", "https:")) else None)
            page.goto(report.as_uri(), wait_until="load")
            page.evaluate("document.fonts.ready")
            state = page.evaluate(r"""() => ({
              viewport: innerWidth, documentWidth: document.documentElement.scrollWidth,
              mathCount: document.querySelectorAll('math').length,
              fontLoaded: document.fonts.check('18px STIX'),
              rawTex: /\\\(|\\\[|\$[^$]+\$/.test(document.body.innerText),
              mathBoxes: [...document.querySelectorAll('math')].map(e=>({width:e.getBoundingClientRect().width,height:e.getBoundingClientRect().height}))
            })""")
            need(state["viewport"] == width and state["documentWidth"] == width, "page overflow")
            need(state["mathCount"] >= 20 and state["fontLoaded"] and not state["rawTex"], "offline mathematics rendering")
            need(all(box["width"] > 0 and box["height"] > 0 for box in state["mathBoxes"]), "nonempty MathML layout")
            need(not errors and not network, "standalone report must not load network resources or raise page errors")
            screenshot = args.out / (name + ".png")
            page.screenshot(path=str(screenshot), full_page=True)
            records.append(dict(name=name, **state, errors=errors, network_requests=network, screenshot_sha256=sha(screenshot)))
            page.close()
        browser.close()
    need(sha(report) == identity, "report changed during browser inspection")
    result = dict(status="PASS_ACTUAL_OFFLINE_MOBILE_DESKTOP_MATHML", report_sha256=identity,
                  playwright_version=importlib.metadata.version("playwright"), chromium=str(executable),
                  chromium_sha256=sha(executable), records=records,
                  visual_inspection_separate=True)
    temporary = args.out / "RESULT.json.tmp"
    temporary.write_text(json.dumps(result, indent=2) + "\n")
    temporary.replace(args.out / "RESULT.json")
    print(json.dumps({"status": result["status"], "out": str(args.out), "math_nodes": records[0]["mathCount"]}))


if __name__ == "__main__":
    main()
