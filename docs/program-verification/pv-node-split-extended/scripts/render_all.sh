#!/usr/bin/env bash
# Render every Markdown deliverable to standalone HTML + PDF (agentB/reports/md_to_report.py, playwright chromium),
# and the summary HTML to PDF. Output: pv8_study/rendered/.
set -eu
B=/ryu/hyunsik/playground/independence/ieantn_qrh/agentB; D=$B/pv8_study; O=$D/rendered; mkdir -p $O
export REPORT_FOOTER="Agent B (Claude) · PV node-split study, extended · hs-chae/IEANTN_test qrh-2pv_B 3280a3c, upstream teorth/IEANTN 466b41b · disposable local worktrees, nothing pushed · no Comparator run · 2026-11-06"
export REPORT_EXTRA_STYLE="table{page-break-inside:auto}tr{page-break-inside:avoid}td,th{font-size:12px}"
for f in EXTENDED_STUDY CASEBOOK MATCHED_EXPERIMENTS MUTATION_TESTS RULE_STRESS_TEST REPRODUCIBILITY MAINTAINER_DECISION; do
  /usr/bin/python3 $B/reports/md_to_report.py $D/docs/PV_NODE_SPLIT_$f.md $O/PV_NODE_SPLIT_$f.html "Agent B · 2026-11-06 · extended study of program verification and IEANTN nodes"
done
/home/hsc/miniconda3/bin/python3 - <<'PY'
import asyncio, pathlib
from playwright.async_api import async_playwright
src = pathlib.Path("/ryu/hyunsik/playground/independence/ieantn_qrh/agentB/pv8_study/docs/PV_NODE_SPLIT_EXTENDED_SUMMARY.html")
out = pathlib.Path("/ryu/hyunsik/playground/independence/ieantn_qrh/agentB/pv8_study/rendered/PV_NODE_SPLIT_EXTENDED_SUMMARY.pdf")
async def go():
    async with async_playwright() as p:
        b = await p.chromium.launch(); pg = await b.new_page()
        await pg.goto("file://" + str(src)); await pg.wait_for_timeout(800)
        await pg.set_viewport_size({"width": 390, "height": 900}); sw = await pg.evaluate("document.documentElement.scrollWidth")
        await pg.set_viewport_size({"width": 1100, "height": 900})
        await pg.add_style_tag(content="@page{size:A4;margin:14mm} body{font-size:13.5px}")
        await pg.pdf(path=str(out), format="A4", print_background=True)
        await pg.screenshot(path=str(out.with_suffix(".png")), full_page=False)
        await b.close(); return sw
sw = asyncio.run(go())
from pypdf import PdfReader
r = PdfReader(str(out)); print(f"{out.name}: pages={len(r.pages)} mobile_scrollWidth={sw}")
PY
cp $D/docs/PV_NODE_SPLIT_EXTENDED_SUMMARY.html $O/
ls -la $O
