# Actual standalone-report browser QA

`check_report_browser.py` opens the actual complete single report in offline Chromium. It checks desktop 1280×900, phone390×844 and narrowphone320×740. The fixed Playwright version is1.62.0; the recorded browser is Chromium153.0.8010.12, build1243. Install the pinned Python dependency with requirements-browser.txt and supply the corresponding Chromium executable through --browser when its local location differs.

```sh
python3 Solutions/RH080Study.v1/reports/check_report_browser.py \
  --html /absolute/network/Solutions/RH080Study.v1/reports/RH080_COMPLETE_REPORT_EN.html \
  --repository /absolute/network \
  --output /absolute/fresh/browser-run
```

Repeat with python3 -O and python3 -OO using fresh output paths. A RESULT is published atomically only after every viewport succeeds. The source HTML, source metadata and checker bytes are frozen/read back, with exact hashes. All current MathML elements must render with nonzero boxes, and actual π/theta glyph fonts are inspected through Chrome's font API. The standalone file must load without HTTP/HTTPS requests or separate local assets. Source-vs-browser paragraph equality detects swallowed or repaired prose HTML. Every internal anchor is exercised with actual keyboard Enter, as are the skip link and horizontal formula/table scrolling. The checks cover page overflow, scroll-container bounds, embedded font bytes and the contrast of the header's source-pin line.

The initial screen must show the first numerical achievement on all three viewports. Source metadata and detailed contents start collapsed; actual Enter opens them and Space closes them. Paragraph equality includes their hidden source-pin prose. The summary precedes the contents, and every contents link remains keyboard accessible after opening it.

Critical long formulas receive left and right screenshots, so a phone reader can recover their domains and endpoints by panning. First-view, overview, source boundary, population, exposure, audit-scope and resource screenshots are also preserved. The checker records screenshots as evidence; a human reviewer separately inspects the actual images.

This is a rendering/accessibility acceptance check, not a new mathematical proof or an audit of completed experimental outcomes. Draft source-pin links are recorded against local Git objects without being silently treated as a final release success. For the final published source checkpoint, require the separate source-link gate:

```sh
python3 Solutions/RH080Study.v1/reports/check_report_browser.py \
  --html /absolute/network/Solutions/RH080Study.v1/reports/RH080_COMPLETE_REPORT_EN.html \
  --repository /absolute/network \
  --verify-source-links \
  --output /absolute/fresh/final-browser-release-run
```

That flag requires every source hyperlink to use the declared exact revision and to exist in its local Git object. Remote publication/attachment verification remains a separate root publication gate. This checker does not visit remote papers or GitHub pages.

Exercise actual rejection paths under normal/-O/-OO:

```sh
python3 Solutions/RH080Study.v1/reports/test_report_browser_cli.py \
  --html /absolute/network/Solutions/RH080Study.v1/reports/RH080_COMPLETE_REPORT_EN.html \
  --output /absolute/fresh/browser-negative-controls
```

The39 cases reject stale output paths, malformed viewports, incorrect input hashes/counts, script-bearing input, absent MathML, duplicate/non-finite JSON, a missing source-gate repository, changed embedded font bytes and boolean counts. Six cases launch the real browser against deliberately low-contrast or page-overflow CSS. These are input/rendering rejection tests, not mathematical counterexamples. Every acceptance/rejection check uses explicit errors, not assert or __debug__.

Output directories must be fresh and are experiment-owned. They contain the exact private frozen report/checker input, compact JSON receipts and PNG screenshots. They are reproducible and do not alter the one public primary report. Retain essential receipts/screenshots; do not mistake an earlier report's QA receipt for a changed final report's acceptance.
