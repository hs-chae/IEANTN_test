#!/usr/bin/env python3
"""Real original-proof/dependency controls and actual CLI rejection in 3 modes.

Fixtures are guard tests only; they never produce a mathematical result receipt.
The running original study is read-only throughout.
"""
from pathlib import Path
import argparse, ast, copy, importlib.util, json, os, subprocess, sys, tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import recovery_origin as origin

def load():
    spec = importlib.util.spec_from_file_location('resource_count_v2', HERE/'recover_count_v2.py')
    e = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = e
    spec.loader.exec_module(e)
    return e

def worker():
    e, v = load(), origin.engine()
    rows = []
    def reject(name, function):
        try:
            function()
        except (ValueError, FileNotFoundError, KeyError, TypeError):
            rows.append(dict(name=name, status='REJECT'))
        else:
            raise RuntimeError('mutation accepted: '+name)
    old_tree = ast.parse((HERE/'recover_count.py').read_text())
    new_tree = ast.parse((HERE/'recover_count_v2.py').read_text())
    for name in ['leaf_text', 'closed_consumer', 'reports', 'required', 'command', 'imports']:
        left = next(x for x in old_tree.body if isinstance(x, ast.FunctionDef) and x.name == name)
        right = next(x for x in new_tree.body if isinstance(x, ast.FunctionDef) and x.name == name)
        e.need(ast.dump(left) == ast.dump(right), 'scientific generator/checker delta: '+name)
    rows.append(dict(name='all_six_scientific_generator_and_axiom_functions_identical', status='PASS'))
    for label, good, bad in [
        ('returncode_false', {'returncode': 0}, {'returncode': False}),
        ('returncode_float', {'returncode': 0}, {'returncode': 0.0}),
        ('resource_false', {'samples': 0}, {'samples': False}),
        ('resource_float', {'samples': 0}, {'samples': 0.0}),
        ('module_range_false', {'range': [0, 32768]}, {'range': [False, 32768]}),
        ('module_range_float', {'range': [0, 32768]}, {'range': [0.0, 32768]}),
    ]:
        reject('strict_JSON_'+label, lambda good=good, bad=bad:
               e.need(origin.exact(good, bad), 'strict JSON type distinction'))
    m = v.read(origin.ORIGIN/'MANIFEST.json')
    q = next(q for q in m['modules'] if q['kind'] == 'arithmetic' and
             (origin.ORIGIN/'attempts'/q['module']/'ACCEPTED.json').exists())
    actual = v.read(origin.ORIGIN/'attempts'/q['module']/'ACCEPTED.json')
    proof = v.audit_receipt(origin.ORIGIN, m, q, Path(actual['receipt']))
    e.need(proof == actual['proof'] and not proof['axioms'][v.required(q)[0]],
           'actual original empty-axiom arithmetic witness')
    rows.append(dict(name='actual_original_source_object_command_log_EMPTY_readback', status='PASS',
                     module=q['module'], receipt=actual['receipt']))
    for text in ["'Exact.part' depends on axioms: [propext]",
                 "'Exact.part' depends on axioms: [Lean.ofReduceBool]",
                 "'Exact.part' depends on axioms: [sorryAx]", '']:
        reject('invalid_numerical_axiom_report_'+str(len(rows)),
               lambda text=text: e.reports(text, ['Exact.part'], True))
    with tempfile.TemporaryDirectory(prefix='rh-count-v2-controls-') as d:
        root = Path(d)
        e.save(root/'ORIGIN_CHECKPOINT.json', dict(origin=str(origin.ORIGIN), records=[actual]))
        e.need(e.audit_receipt(root, m, q, Path(actual['receipt'])) == proof,
               'actual original receipt transported without relabeling command')
        rows.append(dict(name='positive_actual_reused_proof_route', status='PASS'))
        for key, value in [('source_sha256', '0'*64), ('returncode', False),
                           ('returncode', 0.0), ('peak_RSS_bytes', float(proof['peak_RSS_bytes']))]:
            bad = copy.deepcopy(actual)
            bad['proof'][key] = value
            e.save(root/'ORIGIN_CHECKPOINT.json', dict(origin=str(origin.ORIGIN), records=[bad]))
            reject('changed_origin_proof_'+key,
                   lambda: e.audit_receipt(root, m, q, Path(actual['receipt'])))
        reject('wrong_reused_receipt_location',
               lambda: e.audit_receipt(root, m, q, root/'forged.json'))
        target = root/'dependency'
        probe = origin.dependency_probe(v, origin.ORIGIN/'source', origin.ORIGIN/'union',
                                        m['context'], q['module'], target)
        records = []
        for row in m['modules']:
            p = origin.ORIGIN/'attempts'/row['module']/'ACCEPTED.json'
            if p.exists():
                records.append(v.read(p))
        objects = origin.object_map(v, origin.ORIGIN, m, records)
        required = origin.direct_imports(v, origin.ORIGIN, m, q['module'])
        origin.audit_probe(v, probe, origin.ORIGIN/'source', m['context'], target, objects, required)
        e.save(root/'DEPENDENCY_PROBE.json', probe)
        e.audit_compiled_probe(origin.ORIGIN, m, q, root, objects)
        rows.append(dict(name='actual_dependency_CLI_and_complete_application_imports', status='PASS',
                         command=probe['command']))
        for status in [False, True, 1, -9]:
            bad = dict(probe, returncode=status)
            reject('probe_returncode_'+str(status), lambda bad=bad:
                origin.audit_probe(v, bad, origin.ORIGIN/'source', m['context'], target, objects, required))
        text = (target/'stdout').read_text()
        other = next(row for row in m['modules'] if row['kind'] == 'arithmetic'
                     and row['module'] != q['module'])
        bad = dict(probe, module=other['module'])
        e.save(root/'DEPENDENCY_PROBE.json', bad)
        reject('substitute_another_module_dependency_probe', lambda:
               e.audit_compiled_probe(origin.ORIGIN, m, q, root, objects))
        (target/'stdout').write_text('')
        bad = dict(probe, stdout_sha256=v.sha(target/'stdout'))
        reject('empty_dependency_output_and_updated_hash', lambda:
            origin.audit_probe(v, bad, origin.ORIGIN/'source', m['context'], target, objects, required))
        # Even if an attacker updates the output hash, omitting a necessary
        # direct application object or inserting a foreign object must reject.
        dropped = [s for s in text.splitlines() if Path(s).resolve() != required[0]]
        (target/'stdout').write_text('\n'.join(dropped)+'\n')
        bad = dict(probe, stdout_sha256=v.sha(target/'stdout'))
        reject('drop_required_dependency_and_update_hash', lambda:
            origin.audit_probe(v, bad, origin.ORIGIN/'source', m['context'], target, objects, required))
        (target/'stdout').write_text(text+'/tmp/foreign-unverified-application.olean\n')
        bad = dict(probe, stdout_sha256=v.sha(target/'stdout'))
        reject('foreign_dependency_and_updated_hash', lambda:
            origin.audit_probe(v, bad, origin.ORIGIN/'source', m['context'], target, objects, required))
        (target/'stdout').write_text(text)
        # Original is still live: this must reject; no signal is sent.
        reject('live_origin_cannot_be_migrated', lambda: origin.drained(v, origin.ORIGIN))
        duplicate = root/'duplicate.json'
        duplicate.write_text('{"a":1,"a":2}')
        reject('duplicate_JSON_key', lambda: e.read(duplicate))
        duplicate.write_text('{"a":NaN}')
        reject('nonfinite_JSON', lambda: e.read(duplicate))
    print(json.dumps(dict(status='PASS_RESOURCE_V2_GUARD_CONTROLS',
                          optimization=sys.flags.optimize, rows=rows)))

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--worker', action='store_true')
    p.add_argument('--out', type=Path)
    a = p.parse_args()
    if a.worker:
        worker()
        return
    if a.out is None or a.out.exists():
        raise ValueError('fresh --out receipt required')
    e = load()
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    results = []
    for flags in [[], ['-O'], ['-OO']]:
        cp = subprocess.run([sys.executable, *flags, str(Path(__file__).resolve()), '--worker'],
                            env=env, capture_output=True, text=True)
        e.need(cp.returncode == 0, 'actual controls failed: '+cp.stderr)
        row = json.loads(cp.stdout)
        with tempfile.TemporaryDirectory(prefix='rh-count-v2-cli-') as d:
            for route in ['--verify', '--check']:
                cmd = [sys.executable, *flags, str(HERE/'recover_count_v2.py'), route, d]
                bad = subprocess.run(cmd, env=env, capture_output=True, text=True)
                e.need(bad.returncode != 0, 'incomplete actual CLI accepted')
                row['rows'].append(dict(name='actual_V2_CLI_'+route,
                                        status='REJECT', command=cmd))
        results.append(row)
    receipt = dict(status='PASS_ALL_THREE_PYTHON_MODES_RESOURCE_ONLY_V2', results=results,
        controller_sha256=e.sha(HERE/'recover_count_v2.py'),
        helper_sha256=e.sha(HERE/'recovery_origin.py'),
        control_source_sha256=e.sha(__file__), no_original_data_or_worker_mutation=True,
        scope='Real reused arithmetic proof and actual dependency CLI guard checks, plus negative actual acceptance routes; not a completed count.')
    e.save(a.out, receipt)
    print(receipt['status'])

if __name__ == '__main__':
    main()
