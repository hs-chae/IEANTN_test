#!/usr/bin/env bash
# Full deterministic data regeneration + fresh source replay; no old appobjects.
set -euo pipefail
LOCAL_REPRO_SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
LOCAL_REPRO_SOURCE_DIR=$(cd -- "$LOCAL_REPRO_SCRIPT_DIR/.." && pwd)
if [[ "${1:-}" == "--prepared" ]]; then
  [[ $# -ge 2 && $# -le 4 ]] || { echo 'Usage: --prepared OUT [CPUS] [JOBS]' >&2; exit 2; }
  LOCAL_REPRO_OUTPUT=$2
  LOCAL_REPRO_CPUS=${3:-84,85,86,87,88,89}
  LOCAL_REPRO_JOBS=${4:-6}
else
  [[ $# -ge 2 && $# -le 4 ]] || { echo 'Usage: CONTEXT OUT [CPUS] [JOBS]' >&2; exit 2; }
  LOCAL_REPRO_CONTEXT=$1
  LOCAL_REPRO_OUTPUT=$2
  LOCAL_REPRO_CPUS=${3:-84,85,86,87,88,89}
  LOCAL_REPRO_JOBS=${4:-6}
  python3 "$LOCAL_REPRO_SCRIPT_DIR/reproduce_local_million.py" --context "$LOCAL_REPRO_CONTEXT" \
    --out "$LOCAL_REPRO_OUTPUT" --mode full --prepare-only --jobs "$LOCAL_REPRO_JOBS" \
    --memory-gib 48 --cpus "$LOCAL_REPRO_CPUS"
fi
# Only install the tested RESOURCE driver/profile into an otherwise immutable
# generated workspace. All mathematical and generated Lean files stay fixed.
python3 - "$LOCAL_REPRO_SOURCE_DIR" "$LOCAL_REPRO_OUTPUT" <<'PY'
from pathlib import Path
import hashlib,json,shutil,sys
source=Path(sys.argv[1]).resolve();out=Path(sys.argv[2]).resolve();workspace=out/'network/Solutions/RamanujanSourcePV.v1'
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
p=read(out/'PREPARED.json');g=read(out/'GENERATED_SOURCES.json');need(p['status']=='PREPARED_ONLY_NO_LEAN_REPLAY_OR_MATH_ACCEPTANCE'and p['mode']=='full'and g['exact_accepted_bytes_checked']is True and len(g['sources'])==958,'exact full prepared source universe')
for item in g['sources']:need(sha(item['source'])==item['sha256'],'every exact generated mathematical source')
snapshot=read(out/'SOURCE_SNAPSHOT.json');plan=read(out/'PLAN.json')
for item in snapshot['files']:
 path=Path(item['clone'])
 if path==workspace/'BUILD_CONTEXT.json':continue
 need(sha(path)==item['sha256'],'frozen original source/payload')
need(sha(workspace/'BUILD_CONTEXT.json')==plan['cloned_context_sha256'],'explicit clean context identity')
need(not(out/'build').exists(),'fresh full proof object bank')
records=[]
for relative in ['scripts/reproduce_profiled_closure.py','evidence/COLD_MODULE_MEMORY_PROFILES.json']:
 original=source/relative;target=workspace/relative
 if target.exists():need(sha(target)==sha(original),'existing frozen driver matches tested source')
 else:target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(original,target)
 records.append({'source':str(original),'clone':str(target),'sha256':sha(target)})
receipt=out/'RESOURCE_DRIVER_OVERLAY.json';need(not receipt.exists(),'fresh resource overlay receipt');receipt.write_text(json.dumps({'only_resource_driver_and_profile_added':True,'mathematical_sources_changed':False,'records':records},indent=2)+'\n')
PY
LOCAL_REPRO_WORKSPACE="$LOCAL_REPRO_OUTPUT/network/Solutions/RamanujanSourcePV.v1"
python3 "$LOCAL_REPRO_WORKSPACE/scripts/reproduce_profiled_closure.py" \
  --context "$LOCAL_REPRO_WORKSPACE/BUILD_CONTEXT.json" --out "$LOCAL_REPRO_OUTPUT/build" \
  --profile-json "$LOCAL_REPRO_WORKSPACE/evidence/COLD_MODULE_MEMORY_PROFILES.json" \
  --memory-gib 48 --aggregate-gib 300 --jobs "$LOCAL_REPRO_JOBS" --cpus "$LOCAL_REPRO_CPUS" \
  --root RamanujanPV.MillionCriticalSourceClosed --root RamanujanPV.SegmentSourceMargins \
  --root RamanujanPV.SegmentMillionDependencyAudit \
  --theorem RamanujanPV.MillionCriticalSourceClosed.real_interval \
  --theorem RamanujanPV.MillionCriticalSourceClosed.uniform_gap \
  --theorem RamanujanPV.MillionCriticalSourceClosed.p_endpoint_count \
  --theorem RamanujanPV.MillionCriticalSourceClosed.q_endpoint_count \
  --theorem RamanujanPV.SegmentRamanujanMillion.first_1000001_real_interval \
  --theorem RamanujanPV.SegmentSourceMargins.million_gap
python3 "$LOCAL_REPRO_WORKSPACE/scripts/reproduce_profiled_closure.py" --check "$LOCAL_REPRO_OUTPUT/build"
