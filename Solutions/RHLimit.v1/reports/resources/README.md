# Frozen-candidate replay resource figure

This is plotting evidence for the completed frozen-candidate full source replay.
It does not include the later clean-guard or legacy-consumer replays, and it is
not a mathematical proof or a source-first PV claim.

The SVG is standalone with its glyph outlines included. The PNG is a convenient
preview. `inputs/` preserves all three exact datasets; the two rendering receipts
record source, data, font, package and figure hashes. `DETERMINISM.json` confirms
two byte-identical actual SVG and PNG renders after the full replay passed.

## Read the figure

Panel A plots the actual sampled owned-process-tree RSS, in GiB, against minutes
from the resource-wrapper start. Sampling was scheduled every two seconds; this
is not a continuous peak. The RSS sum can count shared pages more than once.
Panel B plots literal route-submission to receipt-acceptance events, against
minutes from the first submission. These spans include receipt validation and
do not assert exact process-start/exit timestamps. The separate clock origins
are retained rather than inventing an alignment. No host-total memory curve,
future projection or comparative performance claim is made.

## Regenerate from a clean environment

Copy this export to a working directory first. Use Python 3.11.14 and the exact
hash-locked plotting packages. No Lean installation or proof bank is required.

```sh
uv venv .venv --python 3.11.14
uv pip sync --python .venv/bin/python --require-hashes requirements.lock.txt
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python generate_resource_figure.py \
  --samples inputs/samples.jsonl \
  --orchestrator inputs/orchestrator.json \
  --resources inputs/resource_state.json \
  --mode final --out regenerated-a
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python generate_resource_figure.py \
  --samples inputs/samples.jsonl \
  --orchestrator inputs/orchestrator.json \
  --resources inputs/resource_state.json \
  --mode final --out regenerated-b
cmp resource-replay.svg regenerated-a/resource-replay.svg
cmp regenerated-a/resource-replay.svg regenerated-b/resource-replay.svg
```

The fixed SVG hash salt and omitted Date metadata make these bytes deterministic
under the recorded environment. The export includes the exact package pins,
package artifact SHA-256 allowlists, the successful actual hash-locked reinstall
receipt/logs, and the pinned wheel's DejaVu and Matplotlib licenses. No virtual
environment, wheel or cache is included.
