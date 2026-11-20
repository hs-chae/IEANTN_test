# Final offline report checks: fresh replay completed

The canonical HTML passed all70 statically rendered MathML expressions at390px and1280px, with its embedded STIX font, no scripts/network requests, and keyboard scrolling for every overflowing table. Mobile tables show instructions and readable first/numerical columns. Exact Playwright/Chromium versions and measured widths/heights are in BROWSER_RESULT.json.

Run the executable controls from a complete published solution:

    python3 control_runner.py --solution /absolute/SOLUTION --out /fresh/CONTROLS

The15 actual normal/-O/-OO routes accept the identical valid report and reject duplicate keys, NaN, overflowing1e999 and a claimed closed global threshold. Input fixtures/stdout/stderr/source snapshot are retained. Generated identical HTML copies are omitted; the canonical report and its SHA are retained.

With the recorded Playwright version and Chromium installed:

    python3 browser_runner.py --report /absolute/FULL_REPORT.html --out /fresh/BROWSER

An early keyboard harness incorrectly demanded scrolling for a table that already fit; another attempt exposed headless focus timing. The final harness explicitly activates the page and waits for actual scrolling only where content overflows. These were harness repairs, with no mathematical-source changes. Historical private build records preserve the attempts.

These are report/acceptance checks, not numerical ANT or C program verification. Scientific theorem receipts remain separate.
