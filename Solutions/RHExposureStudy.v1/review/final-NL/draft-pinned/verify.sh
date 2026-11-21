#!/bin/bash
set -euo pipefail
ROOT=${1:-/work/submission}
OUT=${BUILD_DIR:-/work/rh-verify}
PY=/usr/bin/python3.10
L=/opt/lean/bin/lean
export PYTHONDONTWRITEBYTECODE=1
"$PY" -c 'import pathlib,sys; pathlib.Path(sys.argv[1]).mkdir(parents=True,exist_ok=True)' "$OUT"
export LEAN_PATH="$OUT:/generic/lib/mathlib:/generic/lib/plausible:/generic/lib/LeanSearchClient:/generic/lib/importGraph:/generic/lib/proofwidgets:/generic/lib/aesop:/generic/lib/Qq:/generic/lib/batteries"
export ENVELOPE_OUT="$OUT/ramanujan_cells.json"
export LEAN_CELL_OUT="$OUT/EnvelopeData.lean"
"$PY" "$ROOT/bounds.py"
"$PY" "$ROOT/emit_lean_cells.py"
"$PY" - "$ROOT" "$OUT" <<'PYCODE'
import sys
from pathlib import Path
a,b=map(Path,sys.argv[1:])
for f in ('EnvelopeData.lean','ramanujan_cells.json'):
 assert (a/f).read_bytes()==(b/f).read_bytes(), f
PYCODE
"$PY" "$ROOT/parabola.py"
"$PY" "$ROOT/weighted_small.py"
"$PY" "$ROOT/last_real.py"
"$L" -R "$ROOT" -o "$OUT/PrimeSieveExec.olean" -c "$OUT/PrimeSieveExec.c" "$ROOT/PrimeSieveExec.lean"
for stem in PrimeCountProgram RealConsumers RationalLog CertifiedCrossing RationalEnvelope EnvelopeData; do
  "$L" -R "$ROOT" -o "$OUT/$stem.olean" "$ROOT/$stem.lean"
done
"$L" -R "$ROOT" -c "$OUT/RunPrime.c" "$ROOT/RunPrime.lean"
/opt/lean/bin/leanc -O3 "$OUT/PrimeSieveExec.c" "$OUT/RunPrime.c" -o "$OUT/prime_lean"
"$OUT/prime_lean" 38358837682 14111427770 1630650290176
if [[ "${RUN_NATIVE_DECIDE:-0}" == 1 ]]; then
  "$L" -R "$ROOT" -o "$OUT/NativeCrossing.olean" "$ROOT/NativeCrossing.lean"
fi
if [[ "${RUN_BIG_CXX:-0}" == 1 ]]; then
  /usr/bin/g++ -std=c++17 -O3 -march=x86-64 -pthread "$ROOT/finite_ram.cpp" -o "$OUT/finite_ram"
  "$OUT/finite_ram" 1630650286564 8
fi
