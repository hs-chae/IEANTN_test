"""Prepare a Lean observation comparison from a fresh pinned actual C main run.

The observation is never an expected-output provider for the program. Source/main
computation proofs are already independent; Lean must prove equality to this observation.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path

B = Path(__file__).resolve().parent
R = B.parents[1]


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strict(text):
    def pairs(rows):
        result = {}
        for key, value in rows:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result

    def floating(value):
        x = float(value)
        need(math.isfinite(x), 'nonfinite JSON number')
        return x

    def invalid(value):
        raise ValueError('nonfinite JSON constant ' + value)
    return json.loads(text, object_pairs_hook=pairs, parse_float=floating, parse_constant=invalid)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--run', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--source-output', type=Path, required=True)
    args = ap.parse_args()
    run, out, source = args.run.resolve(), args.out.resolve(), args.source_output.resolve()
    need(run.is_relative_to(R) and out.is_relative_to(R) and source.is_relative_to(R),
         'experiment-owned inputs/outputs required')
    need(not out.exists() and not source.exists() and
         source.name == 'MainObservedOutput.lean' and source.parent.name == 'SynergyHeightC',
         'fresh observation/source targets required')
    pinpath = B / 'height-source-binding-component-v1/CPP_ASSOCIATION_PIN.json'
    pin = strict(pinpath.read_text())
    receiptpath = run / 'RECEIPT.json'
    receipt = strict(receiptpath.read_text())
    rawpath = run / 'output.bin'
    raw = rawpath.read_bytes()
    need(receipt['status'] == 'RAW_ACTUAL_CPP_OUTPUT_ASSOCIATION_PASS' and
         receipt['source_first_PV'] is False, 'separate raw execution receipt required')
    need(len(raw) == 768 * 128 + 128 and sha(rawpath) == receipt['output_sha256'] ==
         pin['expected_output_sha256'], 'exact complete physical output identity')
    source_trees = []
    for tree in [B / 'height-bundle-source-v3',
                 B / 'height-source-binding-component-v1/height-bundle-source-v3']:
        files = {p.name: sha(p) for p in tree.iterdir() if p.is_file()}
        need(files == pin['physical_C_files'], 'actual proof/compiled source tree drift')
        source_trees.append(str(tree.relative_to(R)))
    compiler = Path(receipt['commands'][0][0])
    need(sha(compiler) == pin['compiler_sha256'], 'actual compiler drift')
    tail = raw[-128:]
    lo, hi = int.from_bytes(tail[:64], 'little'), int.from_bytes(tail[64:], 'little')
    bytes_text = ','.join(str(x) for x in tail)
    text = f'''/- Actual observed final128bytes from the pinned unchanged C main.
These are observations compared to the independently source-proved computation,
never replacement numerical providers or new mathematical premises. -/
import SynergyHeightC.MainCompleteModel
namespace SynergyHeightC.MainObservedOutput
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

def total : ProofBox := ⟨{lo},{hi}⟩
def bytes : List Nat := [{bytes_text}]

theorem total_exact : SourceMainBudgetV1.Data.total 768=total :=
  MainFinalTotal.exact_source_total

theorem bytes_exact : bytes=EmitUBuffer.bytes total.lo++EmitUBuffer.bytes total.hi := by
  decide +kernel

theorem actual_source_bytes : bytes=EmitUBuffer.bytes (SourceMainBudgetV1.Data.total 768).lo++
    EmitUBuffer.bytes (SourceMainBudgetV1.Data.total 768).hi :=
  bytes_exact.trans (congrArg
    (fun b : ProofBox=>EmitUBuffer.bytes b.lo++EmitUBuffer.bytes b.hi) total_exact.symm)

theorem actual_source_sum : prefixSum logCellCount=some total :=
  (MainBudgetSourceSum.prefix_value 768 (by decide)).trans (congrArg some total_exact)

theorem observed_upper_word_bound : realWord total.hi ≤ 8433850764/1000000000000 := by
  rw [←total_exact]
  exact MainFinalTotal.source_total_word_bound

#print axioms total_exact
#print axioms bytes_exact
#print axioms actual_source_bytes
#print axioms actual_source_sum
#print axioms observed_upper_word_bound
end SynergyHeightC.MainObservedOutput
'''
    out.mkdir(parents=True)
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(text)
    (out / 'observed-total.bin').write_bytes(tail)
    record = dict(status='OBSERVATION_PREPARED_REQUIRES_LEAN_SOURCE_COMPARISON',
                  script_sha256=sha(Path(__file__)), raw_receipt=str(receiptpath.relative_to(R)),
                  raw_receipt_sha256=sha(receiptpath), physical_output=str(rawpath.relative_to(R)),
                  physical_output_bytes=len(raw), physical_output_sha256=sha(rawpath),
                  total_observation_bytes=128, total_observation_sha256=sha(out / 'observed-total.bin'),
                  lo=str(lo), hi=str(hi), source=str(source.relative_to(R)), source_sha256=sha(source),
                  source_trees=source_trees, source_pin_sha256=sha(pinpath),
                  compiler=str(compiler), compiler_sha256=sha(compiler),
                  qualification='No proof acceptance or new PV claim from preparation. Compare with complete source proof and actual Lean acceptance receipts.')
    temporary = out / 'PREPARATION.pending'
    temporary.write_text(json.dumps(record, indent=2)+'\n')
    os.replace(temporary, out / 'PREPARATION.json')
    print(json.dumps(dict(status=record['status'], output_bytes=len(raw), lo=str(lo), hi=str(hi))))


if __name__ == '__main__':
    main()
