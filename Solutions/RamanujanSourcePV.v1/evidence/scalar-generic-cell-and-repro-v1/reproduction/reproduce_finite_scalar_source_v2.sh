#!/usr/bin/env bash
# V2: complete selected-million source-PV overlay after the clean local-count stage.
# The context must point to that stage's freshly compiled application objects.
set -euo pipefail
scalar_check_only=0
if [ "${1:-}" = --check-prerequisites ]; then scalar_check_only=1; shift; fi
if [ "$#" -ne 4 ]; then
  echo 'Usage: reproduce_finite_scalar_source_v2.sh LOCAL_FINISHED_CONTEXT ORIGINAL_ROWS_DATA FRESH_OUTPUT CPU' >&2
  exit 2
fi
scalar_context=$1
scalar_rows=$2
scalar_out=$3
scalar_cpu=$4
# Task-specific resource overrides; all limits are checked by compile_lean_context.
SCALAR_SOURCE_MEMORY_GIB=${SCALAR_SOURCE_MEMORY_GIB:-96}
SCALAR_NUMERIC_MEMORY_GIB=${SCALAR_NUMERIC_MEMORY_GIB:-24}
SCALAR_FINAL_MEMORY_GIB=${SCALAR_FINAL_MEMORY_GIB:-48}
SCALAR_AUDIT_MEMORY_GIB=${SCALAR_AUDIT_MEMORY_GIB:-96}
scalar_solution=$(cd -- "$(dirname -- "$0")/.." && pwd)
python3 - "$scalar_context" "$scalar_rows" "$scalar_out" "$scalar_cpu" "$scalar_solution" "$scalar_check_only" "$SCALAR_SOURCE_MEMORY_GIB" "$SCALAR_NUMERIC_MEMORY_GIB" "$SCALAR_FINAL_MEMORY_GIB" "$SCALAR_AUDIT_MEMORY_GIB" <<'PREFLIGHT'
from pathlib import Path
import hashlib,json,os,sys
def need(value,message):
    if not value:raise ValueError(message)
def strict(path):
    def pairs(items):
        result={}
        for key,value in items:
            need(key not in result,'duplicate JSON key');result[key]=value
        return result
    return json.loads(Path(path).read_text(),object_pairs_hook=pairs,
        parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
context_path,rows_path,out_path=map(Path,sys.argv[1:4]);cpu=sys.argv[4]
solution=Path(sys.argv[5]).resolve();check_only=sys.argv[6]=='1'
context=strict(context_path);reference=strict(solution/'BUILD_CONTEXT.json');out=out_path.resolve()
objects=Path(context['new_application_object_root']).resolve()
need(out_path.is_absolute() and not out.exists() and out.is_relative_to(objects.parent),'fresh absolute context-owned scalar output required')
limits=[int(value) for value in sys.argv[7:11]]
need(all(1<=value<=300 for value in limits),'bounded1..300GiB resource ceilings')
available=int(next(line.split()[1]for line in Path('/proc/meminfo').read_text().splitlines()if line.startswith('MemAvailable:')))*1024
need(max(limits)*1024**3+512*1024**3<=available,'retain512GiB host reserve')
need(max(limits)<=48 or available>=1024**4,'high-resource replay requires genuinely available1TiB RAM')
need(sha(rows_path)=='054ad58fe66e6b22ef91c06e19c1492fd24c7636c0fc241cba7c3fe760b5294e','exact original285-row scientific source required')
need(sha(context['compiler'])==context['compiler_sha256']==reference['compiler_sha256'],'pinned compiler identity')
need([(d['name'],d['revision'])for d in context['generic_dependencies']]==[(d['name'],d['revision'])for d in reference['generic_dependencies']],'pinned generic dependencies')
need(len(cpu.split(','))==1 and int(cpu) in os.sched_getaffinity(0),'one available scalar replay CPU')
script=solution/'scripts/reproduce_finite_scalar_source_v2.sh';text=script.read_text()
core=text.split("done <<'MODULES'\n",1)[1].split('\nMODULES',1)[0]
order=[line.split()[0] for line in core.splitlines()];future=set(order);seen=set();base=set()
final=['FiniteSourceCells','FiniteSourceRamanujanMillion','FiniteProgramCells','FiniteProgramMillion','FiniteGuardedMillion','FiniteGuardedResult','FiniteProgramDependencyAudit','FiniteGuardedDependencyAudit']
ordered=order+['RamanujanPV.'+name for name in final]
future=set(ordered);numeric={'RamanujanPV.FiniteScalarMillion.'+name for name in ['LogFinal','CellFinal','DomainFinal']}
source_records=[]
for name in ordered:
    path=solution/Path(*name.split('.')).with_suffix('.lean')
    source_records.append({'module':name,'sha256':sha(path)})
    for line in path.read_text().splitlines():
        if line.startswith('import '):
            for dependency in line.removeprefix('import ').split():
                need(dependency not in future or dependency in seen,'source dependency order: '+name+' requires '+dependency)
                if dependency not in seen|numeric and not dependency.startswith(('Mathlib.','Lean.')):base.add(dependency)
    seen.add(name)
for name in sorted(base):
    need((objects/Path(*name.split('.')).with_suffix('.olean')).is_file(),'finished clean-local prerequisite missing: '+name)
print(json.dumps({'status':'PREREQUISITES_ONLY_NOT_REPLAYED' if check_only else'PREREQUISITES_PASS_REPLAY_STARTING','context_sha256':sha(context_path),'rows_sha256':sha(rows_path),'script_sha256':sha(script),'ordered_static_module_count':len(ordered),'base_modules':sorted(base),'source_hashes':source_records},sort_keys=True))
PREFLIGHT
if [ "$scalar_check_only" = 1 ]; then exit 0; fi
mkdir -- "$scalar_out"
python3 "$scalar_solution/scripts/generate_exp_source.py"
python3 "$scalar_solution/scripts/generate_log_source.py"
python3 "$scalar_solution/scripts/generate_cell_source.py"
while read -r scalar_module scalar_memory; do
  if [ "$scalar_memory" = 96 ]; then scalar_memory=$SCALAR_SOURCE_MEMORY_GIB; fi
  python3 "$scalar_solution/scripts/compile_lean_context.py" "$scalar_module" \
    --context "$scalar_context" --cpus "$scalar_cpu" --memory-gib "$scalar_memory"
done <<'MODULES'
RamanujanPV.WideScalar 24
RamanujanPV.FiniteScalarMachine 24
RamanujanPV.FiniteScalarWords 24
RamanujanPV.FiniteScalarRules 24
RamanujanPV.FiniteScalarEval 24
RamanujanPV.FiniteExpSource 48
RamanujanPV.FiniteWideExpExecute 24
RamanujanPV.FiniteWideExpLinked 24
RamanujanPV.FiniteWideExpEnclosures 24
RamanujanPV.FiniteLogSource 96
RamanujanPV.FiniteLogCeil 24
RamanujanPV.FiniteLogServices 24
RamanujanPV.FiniteLogExecution 24
RamanujanPV.FiniteScalarRows 24
RamanujanPV.FiniteCellSource 96
RamanujanPV.FiniteCellExecution 24
RamanujanPV.FiniteCellDecompose 24
RamanujanPV.FinitePredicateBounds 24
RamanujanPV.FiniteCellWords 24
RamanujanPV.FiniteCellProtected 48
RamanujanPV.FiniteCellTrace 24
RamanujanPV.FiniteCellSound 24
RamanujanPV.FiniteCellInverse 48
RamanujanPV.FiniteLogBounds 24
RamanujanPV.FiniteLogNormalizationBounds 24
RamanujanPV.FiniteLogNormalize 24
RamanujanPV.FiniteLogNormalizationUnique 24
RamanujanPV.FiniteLogSeriesRules 24
RamanujanPV.FiniteLogUpperPrefix 24
RamanujanPV.FiniteLogSeriesInit 24
RamanujanPV.FiniteLogSeriesReturn 24
RamanujanPV.FiniteLogSeriesLoop 24
RamanujanPV.FiniteLogSeriesExecute 24
RamanujanPV.FiniteLogUpperExecute 24
RamanujanPV.FiniteCellGeneric 48
MODULES
python3 "$scalar_solution/scripts/generate_scalar_pv_rows.py" --out "$scalar_out/log" \
  --rows-source "$scalar_rows" --rows-sha256 054ad58fe66e6b22ef91c06e19c1492fd24c7636c0fc241cba7c3fe760b5294e --context "$scalar_context"
python3 "$scalar_solution/scripts/generate_scalar_pv_final.py" --proposal "$scalar_out/log/PROPOSAL.json" --context "$scalar_context"
for scalar_index in 0000 0001 0002 0003 0004 0005 0006 0007 0008; do
  python3 "$scalar_solution/scripts/compile_lean_context.py" "RamanujanPV.FiniteScalarMillion.Log$scalar_index" \
    --context "$scalar_context" --source-root "$scalar_out/log/source" --cpus "$scalar_cpu" --memory-gib "$SCALAR_NUMERIC_MEMORY_GIB"
done
python3 "$scalar_solution/scripts/compile_lean_context.py" RamanujanPV.FiniteScalarMillion.LogFinal \
  --context "$scalar_context" --source-root "$scalar_out/log/source" --cpus "$scalar_cpu" --memory-gib "$SCALAR_NUMERIC_MEMORY_GIB"
python3 "$scalar_solution/scripts/generate_cell_source_rows.py" --out "$scalar_out/cell" \
  --original-log-proposal "$scalar_out/log/PROPOSAL.json" --context "$scalar_context"
for scalar_index in 0000 0001 0002 0003 0004 0005 0006 0007 0008; do
  python3 "$scalar_solution/scripts/compile_lean_context.py" "RamanujanPV.FiniteScalarMillion.Cell$scalar_index" \
    --context "$scalar_context" --source-root "$scalar_out/cell/source" --cpus "$scalar_cpu" --memory-gib "$SCALAR_NUMERIC_MEMORY_GIB"
done
python3 "$scalar_solution/scripts/compile_lean_context.py" RamanujanPV.FiniteScalarMillion.CellFinal \
  --context "$scalar_context" --source-root "$scalar_out/cell/source" --cpus "$scalar_cpu" --memory-gib "$SCALAR_NUMERIC_MEMORY_GIB"
python3 "$scalar_solution/scripts/generate_cell_domains.py" --out "$scalar_out/domains" \
  --original-log-proposal "$scalar_out/log/PROPOSAL.json" --context "$scalar_context"
for scalar_index in 0000 0001 0002 0003 0004 0005 0006 0007 0008; do
  python3 "$scalar_solution/scripts/compile_lean_context.py" "RamanujanPV.FiniteScalarMillion.Domain$scalar_index" \
    --context "$scalar_context" --source-root "$scalar_out/domains/source" --cpus "$scalar_cpu" --memory-gib "$SCALAR_NUMERIC_MEMORY_GIB"
done
python3 "$scalar_solution/scripts/compile_lean_context.py" RamanujanPV.FiniteScalarMillion.DomainFinal \
  --context "$scalar_context" --source-root "$scalar_out/domains/source" --cpus "$scalar_cpu" --memory-gib "$SCALAR_NUMERIC_MEMORY_GIB"
python3 "$scalar_solution/scripts/verify_scalar_domains.py" --proposal "$scalar_out/domains/PROPOSAL.json" \
  --original-log-proposal "$scalar_out/log/PROPOSAL.json" --context "$scalar_context" --out "$scalar_out/domain-audit" --cpus "$scalar_cpu"
python3 "$scalar_solution/scripts/verify_scalar_source_receipts.py" --kind log \
  --proposal "$scalar_out/log/PROPOSAL.json" --context "$scalar_context" --out "$scalar_out/log-audit" --cpus "$scalar_cpu"
python3 "$scalar_solution/scripts/verify_scalar_source_receipts.py" --kind cell \
  --proposal "$scalar_out/cell/PROPOSAL.json" --context "$scalar_context" --out "$scalar_out/cell-audit" --cpus "$scalar_cpu"
python3 "$scalar_solution/scripts/observe_finite_scalars_native.py" --out "$scalar_out/native" \
  --rows-source "$scalar_rows" --rows-sha256 054ad58fe66e6b22ef91c06e19c1492fd24c7636c0fc241cba7c3fe760b5294e --context "$scalar_context"
# Complete ordered selected consumer closure, including historical middle stages
# and the strongest guarded/source-byte-linked result. The clean local-count
# prerequisite supplies SegmentRamanujanMillion/SegmentSourceMargins and their
# recursively compiled source/analytic dependencies.
for scalar_consumer in FiniteSourceCells FiniteSourceRamanujanMillion FiniteProgramCells FiniteProgramMillion FiniteGuardedMillion FiniteGuardedResult; do
  python3 "$scalar_solution/scripts/compile_lean_context.py" "RamanujanPV.$scalar_consumer" \
    --context "$scalar_context" --cpus "$scalar_cpu" --memory-gib "$SCALAR_FINAL_MEMORY_GIB"
done
for scalar_audit in FiniteProgramDependencyAudit FiniteGuardedDependencyAudit; do
  python3 "$scalar_solution/scripts/compile_lean_context.py" "RamanujanPV.$scalar_audit" \
    --context "$scalar_context" --cpus "$scalar_cpu" --memory-gib "$SCALAR_AUDIT_MEMORY_GIB"
done
# Authoritative numerical acceptance remains in each fresh atomic audit RESULT.
# This selected result uses actual C strict/e/log/count paths; counts on the
# separate full1.49T scalar dataset are not claimed by the million replay.
echo 'Complete selected million source-PV scalar closure reproduced.'
