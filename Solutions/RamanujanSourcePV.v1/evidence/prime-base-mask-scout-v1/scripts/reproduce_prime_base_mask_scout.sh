#!/usr/bin/env bash
set -euo pipefail
# Rebuild the combined numerical provider only; no historical application cache.
# Usage: bash SCRIPT SOLUTION PINNED_CONTEXT FRESH_OWNED_OUT CPU_CSV
solution=$(realpath "$1")
context=$(realpath "$2")
replay_out=$(realpath -m "$3")
replay_cpus="$4"
python3 - "$solution" "$context" "$replay_out" <<'PY'
from pathlib import Path
import json,sys
s,c,o=map(Path,sys.argv[1:]);ref=json.loads((s/'BUILD_CONTEXT.json').read_text());ctx=json.loads(c.read_text());owned=Path(ref['new_application_object_root']).resolve().parent
if o.exists()or not o.parent.is_dir()or not o.is_relative_to(owned)or o==owned:raise ValueError('fresh output inside entire owned experiment, existing parent required')
if ctx['compiler_sha256']!=ref['compiler_sha256']or [(x['name'],x['revision'])for x in ctx['generic_dependencies']]!=[(x['name'],x['revision'])for x in ref['generic_dependencies']]:raise ValueError('exact original compiler/generic dependency pins required')
if not(s/'evidence/packed-numerical-source-v1/source/RamanujanPV/PackedSievePrimitiveMaskMillion.lean').is_file():raise ValueError('packaged original P proposal source is required')
PY
mkdir "$replay_out"
python3 "$solution/scripts/generate_balanced_mask_data.py" \
  --baseline-source "$solution/evidence/packed-numerical-source-v1/source/RamanujanPV/PackedSievePrimitiveMaskMillion.lean" \
  --out "$replay_out/data" --data-only-4096 --provider-check
python3 "$solution/scripts/generate_prime_base_mask_scout.py" --out "$replay_out/base"
python3 "$solution/scripts/reproduce_guarded_coupled_closure.py" \
  --context "$context" --out "$replay_out/kernel" \
  --application-source-root "$replay_out/data/source" \
  --application-source-root "$replay_out/base/source" \
  --root RamanujanPV.PackedSievePrimeBaseCombinedAudit \
  --theorem RamanujanPV.PrimeBaseMaskScout.CombinedP.original_mask_equality \
  --memory-gib 48 --aggregate-gib 96 --jobs 2 --cpus "$replay_cpus" --host-reserve-gib 512
python3 -OO "$solution/scripts/reproduce_guarded_coupled_closure.py" --check "$replay_out/kernel"
