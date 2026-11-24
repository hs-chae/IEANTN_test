# Rebuild the offline mathematical reports

The installed renderer is KaTeX0.16.47. The lock file records exact package versions and integrity hashes. It runs at build time; reading the resulting HTML requires no JavaScript, CDN or external math font. STIX font bytes and their license are included in the reports directory.

From the repository root, install the pinned Node dependencies into this directory:

```sh
npm ci --ignore-scripts --no-audit --no-fund --prefix Solutions/RHOcticPush.v1/reports/rendering
python3 -B Solutions/RHOcticPush.v1/reports/build_reports.py \
  --status Solutions/RHOcticPush.v1/reports/DRAFT_STATUS.json \
  --katex Solutions/RHOcticPush.v1/reports/rendering/node_modules/katex \
  --out /tmp/rh-reports-fresh
```

Use a fresh output path. The status file selects a dated draft or reviewed result snapshot; it is documentation, not a proof acceptance gate. The final release supplies its final status file separately. For the actual browser checks, use Playwright1.62.0 with its installed Chromium and check_report_browser.py; the recorded receipts distinguish rendering from mathematical/source review.
