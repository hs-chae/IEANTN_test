#!/usr/bin/env python3
"""Additive source/resource readback for the immutable fresh32 proof recipe.

This does not recompile proofs or strengthen their mathematics. It closes the
copied-resource/source-plan readback omissions of the original recipe while
preserving that recipe, its accepted output, and its historical trust labels.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import math
import os
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
ORIGINAL_SHA = 'cccd380b9e7654debacdd910497d411094a9b798f15319b59dc2db406e58fef5'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def strict_json(text):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def finite_float(text):
        value = float(text)
        need(math.isfinite(value), 'nonfinite JSON number')
        return value
    def constant(text):
        raise ValueError('nonfinite JSON number: '+text)
    return json.loads(text, object_pairs_hook=pairs, parse_float=finite_float,
                      parse_constant=constant)


def reader():
    path = HERE/'reproduce_application.py'
    need(sha(path) == ORIGINAL_SHA, 'immutable original application controller')
    spec = importlib.util.spec_from_file_location('high_application_original', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def auditor(modules):
    text = 'import HighDriverContract\nimport Lean\nopen Lean Elab Command\nrun_cmd do\n'
    text += '  let env ← getEnv\n  let mods := #['
    text += ','.join(json.dumps(x) for x in modules)+']\n'
    return text+'''  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, idx) in env.const2ModIdx.toList do
    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous
    if !mods.contains modName.toString then continue
    let some (.thmInfo _) := env.find? name | continue
    let axs ← collectAxioms name
    unless axs.all allowed.contains do throwError "Nonstandard application proof {name}: {axs}"
    let row := Json.mkObj [("name",toJson name.toString),("module",toJson modName.toString),("axioms",toJson (axs.map Name.toString))]
    logInfo m!"HIGH_MAIN_PROOF {row.compress}"
    count := count + 1
  unless count > 0 do throwError "Empty application proof audit"
  logInfo m!"HIGH_MAIN_AUDIT_PASS {count}"
'''


def verify(out):
    out = Path(out).resolve()
    strict_json((out/'RESULT.json').read_text())
    old = reader()
    result = old.verify(out)
    plan = old.source_plan()
    context_path = ROOT/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json'
    context = old.read(context_path)
    need(canonical(result['context']) == canonical(context), 'approved generic context')
    need(result['historical_application_objects_used'] is False, 'fresh application objects')
    need(type(result['seconds']) in [int, float] and math.isfinite(result['seconds'])
         and result['seconds'] >= 0, 'actual finite nonnegative total duration')
    for dep in context['generic_dependencies']:
        cp = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=dep['path'],
                            capture_output=True, text=True)
        need(cp.returncode == 0 and cp.stdout.strip() == dep['revision'],
             'pinned generic dependency revision')
        need(subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--'],
                            cwd=dep['path']).returncode == 0, 'generic tracked-source drift')
    expected = {q['module']: q for q in plan['modules']}
    names = [q['module'] for q in plan['modules']]
    need(len(names) == len(set(names)) == 31, 'exact scientific source universe')
    for row in result['build']:
        mod = row['module']
        path = out/'source'/old.rel(mod)
        obj = out/'objects'/old.rel(mod, '.olean')
        need(path.is_file() and obj.is_file() and not path.is_symlink()
             and not obj.is_symlink(), 'owned regular source and object')
        if mod == 'HighApplicationAudit':
            need(path.read_text() == auditor(names), 'complete generated theorem auditor')
        else:
            need(row['source_sha256'] == expected[mod]['sha256'] == sha(path),
                 'copied source bound to frozen scientific plan: '+mod)
        need(type(row['seconds']) in [int, float] and math.isfinite(row['seconds'])
             and row['seconds'] >= 0, 'actual finite nonnegative compiler duration')
    need(len(plan['resources']) == 4, 'complete original and high C resources')
    for row in plan['resources']:
        path = out/'source'/row['relative']
        need(path.is_file() and not path.is_symlink(), 'owned copied C resource')
        need(sha(path) == row['sha256'], 'copied actual C resource: '+row['relative'])
    for probe in result['dependencies']:
        mod = probe['module']
        paths = {Path(x).resolve() for x in
                 (out/'dependencies'/(mod+'.stdout')).read_text().splitlines()}
        imports = ['HighDriverContract'] if mod == 'HighApplicationAudit' else expected[mod]['imports']
        # Lean --deps lists direct imports; checking every module's direct
        # edges reconstructs the complete recorded application import DAG.
        for dependency in imports:
            if dependency in expected:
                need((out/'objects'/old.rel(dependency, '.olean')).resolve() in paths,
                     'actual application import coverage: '+mod+' -> '+dependency)
    text = (out/'logs/HighApplicationAudit.stdout').read_text()
    proofs = [strict_json(line.split('HIGH_MAIN_PROOF ', 1)[1])
              for line in text.splitlines() if 'HIGH_MAIN_PROOF {' in line]
    need(all(q['module'] in expected and type(q['axioms']) is list for q in proofs),
         'audited theorem module ownership')
    peaks = []
    for row in result['build']:
        text = (out/'logs'/(row['module']+'.resources')).read_text()
        match = re.search(r'Maximum resident set size \(kbytes\): (\d+)', text)
        need(match is not None, 'measured individual-child RAM')
        peaks.append(int(match[1]))
    return dict(status='PASS_COMPLETE_HIGH_APPLICATION_SOURCE_RESOURCE_READBACK',
                original_result_sha256=sha(out/'RESULT.json'),
                original_controller_sha256=ORIGINAL_SHA,
                additive_reader_sha256=sha(__file__),
                copied_scientific_sources=31, copied_C_resources=4,
                actual_compilations=len(result['build']), theorem_rows=len(proofs),
                peak_individual_child_RSS_KiB=max(peaks), aggregate_RSS_sampled=False,
                context_sha256=sha(context_path), optimization=sys.flags.optimize,
                exact_numerical_count_proved=False, new_complete_PV_claim=False)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--verify', required=True, type=Path)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    if args.receipt:
        need(not args.receipt.exists(), 'fresh additive receipt')
    report = verify(args.verify)
    if args.receipt:
        pending = Path(str(args.receipt)+'.pending')
        need(not pending.exists(), 'fresh atomic pending receipt')
        pending.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
        os.replace(pending, args.receipt)
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
