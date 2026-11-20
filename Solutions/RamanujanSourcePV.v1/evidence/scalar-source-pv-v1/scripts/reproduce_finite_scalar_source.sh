#!/usr/bin/env bash
# Source-first finite-scalar overlay after the reproducible local-count stage.
# The context must point to that stage's freshly compiled application objects.
set -euo pipefail
if [ "$#" -lt 4 ]; then
  echo 'Usage: reproduce_finite_scalar_source.sh CONTEXT ORIGINAL_ROWS_DATA FRESH_OUTPUT CPU [FINAL_CONSUMER_MODULE ...]' >&2
  exit 2
fi
scalar_context=$1
scalar_rows=$2
scalar_out=$3
scalar_cpu=$4
shift 4
scalar_solution=$(cd -- "$(dirname -- "$0")/.." && pwd)
python3 - "$scalar_context" "$scalar_rows" "$scalar_out" <<'PREFLIGHT'
from pathlib import Path
import hashlib,json,sys
context_path,rows_path,out_path=map(Path,sys.argv[1:])
context=json.loads(context_path.read_text());out=out_path.resolve()
if out.exists() or not out.is_relative_to(Path(context['new_application_object_root']).resolve().parent):
    raise ValueError('fresh context-owned scalar output required')
if hashlib.sha256(rows_path.read_bytes()).hexdigest()!='054ad58fe66e6b22ef91c06e19c1492fd24c7636c0fc241cba7c3fe760b5294e':
    raise ValueError('exact original285-row scientific source required')
if hashlib.sha256(Path(context['compiler']).read_bytes()).hexdigest()!=context['compiler_sha256']:
    raise ValueError('pinned compiler identity')
PREFLIGHT
mkdir -- "$scalar_out"
python3 "$scalar_solution/scripts/generate_exp_source.py"
python3 "$scalar_solution/scripts/generate_log_source.py"
python3 "$scalar_solution/scripts/generate_cell_source.py"
while read -r scalar_module scalar_memory; do
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
MODULES
python3 "$scalar_solution/scripts/generate_scalar_pv_rows.py" --out "$scalar_out/log" \
  --rows-source "$scalar_rows" --rows-sha256 054ad58fe66e6b22ef91c06e19c1492fd24c7636c0fc241cba7c3fe760b5294e --context "$scalar_context"
python3 "$scalar_solution/scripts/generate_scalar_pv_final.py" --proposal "$scalar_out/log/PROPOSAL.json" --context "$scalar_context"
for scalar_index in 0000 0001 0002 0003 0004 0005 0006 0007 0008; do
  python3 "$scalar_solution/scripts/compile_lean_context.py" "RamanujanPV.FiniteScalarMillion.Log$scalar_index" \
    --context "$scalar_context" --source-root "$scalar_out/log/source" --cpus "$scalar_cpu" --memory-gib 24
done
python3 "$scalar_solution/scripts/compile_lean_context.py" RamanujanPV.FiniteScalarMillion.LogFinal \
  --context "$scalar_context" --source-root "$scalar_out/log/source" --cpus "$scalar_cpu" --memory-gib 24
python3 "$scalar_solution/scripts/generate_cell_source_rows.py" --out "$scalar_out/cell" \
  --original-log-proposal "$scalar_out/log/PROPOSAL.json" --context "$scalar_context"
for scalar_index in 0000 0001 0002 0003 0004 0005 0006 0007 0008; do
  python3 "$scalar_solution/scripts/compile_lean_context.py" "RamanujanPV.FiniteScalarMillion.Cell$scalar_index" \
    --context "$scalar_context" --source-root "$scalar_out/cell/source" --cpus "$scalar_cpu" --memory-gib 24
done
python3 "$scalar_solution/scripts/compile_lean_context.py" RamanujanPV.FiniteScalarMillion.CellFinal \
  --context "$scalar_context" --source-root "$scalar_out/cell/source" --cpus "$scalar_cpu" --memory-gib 24
python3 "$scalar_solution/scripts/generate_cell_domains.py" --out "$scalar_out/domains" \
  --original-log-proposal "$scalar_out/log/PROPOSAL.json" --context "$scalar_context"
for scalar_index in 0000 0001 0002 0003 0004 0005 0006 0007 0008; do
  python3 "$scalar_solution/scripts/compile_lean_context.py" "RamanujanPV.FiniteScalarMillion.Domain$scalar_index" \
    --context "$scalar_context" --source-root "$scalar_out/domains/source" --cpus "$scalar_cpu" --memory-gib 24
done
python3 "$scalar_solution/scripts/compile_lean_context.py" RamanujanPV.FiniteScalarMillion.DomainFinal \
  --context "$scalar_context" --source-root "$scalar_out/domains/source" --cpus "$scalar_cpu" --memory-gib 24
python3 "$scalar_solution/scripts/verify_scalar_domains.py" --proposal "$scalar_out/domains/PROPOSAL.json" \
  --original-log-proposal "$scalar_out/log/PROPOSAL.json" --context "$scalar_context" --out "$scalar_out/domain-audit" --cpus "$scalar_cpu"
python3 "$scalar_solution/scripts/compile_lean_context.py" RamanujanPV.FiniteProgramCells \
  --context "$scalar_context" --cpus "$scalar_cpu" --memory-gib 48
python3 "$scalar_solution/scripts/compile_lean_context.py" RamanujanPV.FiniteProgramMillion \
  --context "$scalar_context" --cpus "$scalar_cpu" --memory-gib 48
python3 "$scalar_solution/scripts/verify_scalar_source_receipts.py" --kind log \
  --proposal "$scalar_out/log/PROPOSAL.json" --context "$scalar_context" --out "$scalar_out/log-audit" --cpus "$scalar_cpu"
python3 "$scalar_solution/scripts/verify_scalar_source_receipts.py" --kind cell \
  --proposal "$scalar_out/cell/PROPOSAL.json" --context "$scalar_context" --out "$scalar_out/cell-audit" --cpus "$scalar_cpu"
python3 "$scalar_solution/scripts/observe_finite_scalars_native.py" --out "$scalar_out/native" \
  --rows-source "$scalar_rows" --rows-sha256 054ad58fe66e6b22ef91c06e19c1492fd24c7636c0fc241cba7c3fe760b5294e --context "$scalar_context"
for scalar_consumer in "$@"; do
  python3 "$scalar_solution/scripts/compile_lean_context.py" "$scalar_consumer" \
    --context "$scalar_context" --cpus "$scalar_cpu" --memory-gib 48
done
# Authoritative acceptance is in each fresh atomic audit RESULT.json.
# Protected source correctness and all non-strict premises now feed the actual final million theorem.
echo 'Finite scalar sources, numerical executions and exhaustive audits reproduced.'
