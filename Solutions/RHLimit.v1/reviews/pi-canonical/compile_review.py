#!/usr/bin/env python3
"""Independently recompile the exact final24 over the hash-checked fresh316.

This is a canonical-consumer append, not a second cold340 replay or source-first
PV claim. Parent run receipts and every inherited application object are bound.
"""
from pathlib import Path
import argparse, csv, hashlib, json, math, os, re, resource, subprocess, sys, time

R = Path(__file__).resolve().parent
S = R.parents[1]
N = R.parents[3]


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    def pairs(rows):
        result = {}
        for key, value in rows:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result

    def finite(raw):
        value = float(raw)
        need(math.isfinite(value), 'nonfinite JSON')
        return value

    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs,
                      parse_float=finite,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def save(path, value):
    pending = path.with_name('.' + path.name + '.pending')
    need(not pending.exists(), 'stale pending receipt')
    pending.write_text(json.dumps(value, indent=2) + '\n')
    os.replace(pending, path)


def audit(output):
    need('sorryAx' not in output, 'admitted proof in compiler output')
    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    need(len(rows) == len({name for name, _ in rows}), 'duplicate audit declaration')
    result = []
    for name, raw in rows:
        axioms = [x.strip() for x in raw.split(',') if x.strip()]
        need(set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'},
             'nonstandard execution/other axiom: ' + name)
        result.append({'theorem': name, 'axioms': axioms})
    return result


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    for name in ['pi', 'resources', 'spectral', 'integrated', 'out']:
        p.add_argument('--' + name, type=Path, required=True)
    p.add_argument('--scope', type=Path, default=R / 'SCOPE_FINAL.json')
    a = p.parse_args()
    scope = read(a.scope)
    need(scope['stage'] == 'FROZEN_ROOT_HANDOFF_FOR_FINAL_REVIEW', 'unfrozen review scope')
    scope_csv_hash = sha(R / 'scope.csv')
    identities = list(csv.DictReader((R / 'scope.csv').open()))
    expected_theorems = {row['lean_name'] for row in identities if row['kind'] == 'theorem'}
    need(len(identities) == 53 and len(expected_theorems) == 17,
         'exact reviewed53 identities and17 distinct theorem names')
    for row in scope['files']:
        need(sha(N / row['path']) == row['sha256'], 'frozen reviewed source changed')
    out = a.out.resolve()
    need(not out.exists(), 'fresh output required')
    need(out.is_relative_to(Path('/data/ivy-rh-limit-20261122/reviews/pi-canonical')),
         'review-owned output required')
    cli = [sys.executable, str(S / 'scripts/reproduce_integration.py'),
           '--basis', str(a.pi), '--resource-replay', str(a.resources),
           '--spectral', str(a.spectral), '--out', str(out), '--check']
    preflight = subprocess.run(cli, text=True, capture_output=True)
    need(preflight.returncode == 0 and
         'PASS_COMPLETE_FRESH316_AND_FINAL24_SOURCE_PREFLIGHT' in preflight.stdout,
         'parent preflight rejected: ' + preflight.stdout + preflight.stderr)
    parent = read(a.integrated / 'RESULT.json')
    need(parent['status'] == 'PASS_COMPLETE_340_SOURCE_NETWORK_EVOLUTION_CONSUMERS',
         'actual completed340 proof run required')
    for key, folder in [('basis_RESULT_sha256', a.pi),
                        ('spectral_RESULT_sha256', a.spectral),
                        ('resource_replay_RESULT_sha256', a.resources)]:
        need(parent[key] == sha(folder / 'RESULT.json'), 'parent proof association')
    need(parent['BUILD_sha256'] == sha(a.integrated / 'BUILD.json'), 'parent final BUILD')
    m = read(S / 'integration/SOURCE_CLOSURE.json')
    need(parent['source_manifest_sha256'] == sha(S / 'integration/SOURCE_CLOSURE.json'),
         'parent final source manifest')
    need(len(m['modules']) == 24, 'exact selected24')
    basis = read(S / 'pi/SOURCE_CLOSURE.json')['modules']
    spectral = read(S / 'spectral/SOURCE_CLOSURE.json')['modules']
    need(len(basis) == 261 and len(spectral) == 55, 'exact inherited316')
    resource_build = read(a.resources / 'BUILD.json')
    resource_names = {row['module'] for row in resource_build['modules']}
    need(len(resource_names) == 23 and resource_build['status'] == 'PASS', 'C-resource23')
    inherited = []
    done = set()
    for folder, rows in [(a.pi, basis), (a.spectral, spectral)]:
        actual = {r['module']: r for r in read(folder / 'BUILD.json')['modules']}
        for row in rows:
            mod = row['module']
            bank = a.resources if mod in resource_names else folder
            got = next(x for x in resource_build['modules'] if x['module'] == mod) if mod in resource_names else actual[mod]
            need(mod not in done and set(row['application_imports']) <= done,
                 'inherited source order or identity')
            need(type(got['returncode']) is int and got['returncode'] == 0, 'inherited compiler failure')
            rel = mod.replace('.', '/')
            need(sha(N / row['path']) == row['sha256'] == got['source_sha256'],
                 'inherited frozen source')
            need(sha(bank / 'objects' / (rel + '.olean')) == got['object_sha256'],
                 'inherited object')
            inherited.append({'module': mod, 'path': str(bank / 'objects' / (rel + '.olean')),
                              'sha256': got['object_sha256']})
            done.add(mod)
    need(len(done) == 316, 'unique316')
    ctx_path = N / 'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json'
    ctx = read(ctx_path)
    need(sha(ctx['compiler']) == ctx['compiler_sha256'], 'pinned compiler')
    available = next(int(x.split()[1]) << 10 for x in Path('/proc/meminfo').read_text().splitlines()
                     if x.startswith('MemAvailable:'))
    need(available >= (512 + 80) << 30, 'host RAM reserve')
    out.mkdir(parents=True)
    src, obj, union, logs = [out / x for x in ['source', 'objects', 'union', 'logs']]
    for folder in [src, obj, union, logs]:
        folder.mkdir()
    (out / 'controller.executed.py').write_bytes(Path(__file__).read_bytes())
    (out / 'SOURCE_CLOSURE.executed.json').write_bytes((S / 'integration/SOURCE_CLOSURE.json').read_bytes())
    save(out / 'INHERITED316.json', inherited)
    for row in inherited:
        link = union / (row['module'].replace('.', '/') + '.olean')
        link.parent.mkdir(parents=True, exist_ok=True)
        link.symlink_to(row['path'])
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(union), *ctx['generic_libraries']])
    rows, audits = [], []
    started = time.monotonic()
    for row in m['modules']:
        mod = row['module']
        need(mod not in done and set(row['application_imports']) <= done, 'selected source order')
        rel = mod.replace('.', '/')
        f, o = src / (rel + '.lean'), obj / (rel + '.olean')
        f.parent.mkdir(parents=True, exist_ok=True)
        o.parent.mkdir(parents=True, exist_ok=True)
        need(sha(N / row['path']) == row['sha256'], 'selected frozen source')
        f.write_bytes((N / row['path']).read_bytes())
        command = ['/usr/bin/time', '-v', ctx['compiler'], '--root=' + str(src),
                   '-j8', '-o', str(o), str(f)]
        before = time.monotonic()
        cp = subprocess.run(command, cwd=src, env=env, capture_output=True, text=True,
                            preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_AS, (80 << 30, 80 << 30)))
        so, se = logs / (mod + '.stdout'), logs / (mod + '.stderr')
        so.write_text(cp.stdout)
        se.write_text(cp.stderr)
        match = re.search(r'Maximum resident set size \(kbytes\): (\d+)', cp.stderr)
        rr = {'module': mod, 'source_sha256': sha(f), 'returncode': cp.returncode,
              'seconds': time.monotonic() - before, 'command': command,
              'peak_RSS_KiB': int(match[1]) if match else None,
              'stdout_sha256': sha(so), 'stderr_sha256': sha(se)}
        if cp.returncode == 0:
            rr['object_sha256'] = sha(o)
        rows.append(rr)
        save(out / 'BUILD.json', {'status': 'RUNNING' if cp.returncode == 0 else 'FAIL', 'modules': rows})
        need(cp.returncode == 0 and match is not None, 'independent compile: ' + mod)
        audits.extend(audit(cp.stdout))
        link = union / (rel + '.olean')
        link.parent.mkdir(parents=True, exist_ok=True)
        link.symlink_to(o)
        done.add(mod)
        print(len(rows), 24, mod, round(rr['seconds'], 2), flush=True)
    need(len(done) == 340, 'complete selected union')
    need(set(m['final_roots']) <= {x['theorem'] for x in audits}, 'actual final consumer audits absent')
    need(expected_theorems <= {x['theorem'] for x in audits},
         'scoped canonical theorem axiom audit absent')
    need(sha(R / 'scope.csv') == scope_csv_hash, 'written-source identity drift')
    for row in scope['files']:
        need(sha(N / row['path']) == row['sha256'], 'review scope drift during compile')
    for row in m['modules']:
        need(sha(N / row['path']) == row['sha256'], 'final manifest drift during compile')
    save(out / 'BUILD.json', {'status': 'PASS', 'modules': rows})
    save(out / 'RESULT.json', {
        'status': 'PASS_INDEPENDENT_FROZEN24_CANONICAL_APPEND_OVER_VERIFIED_FRESH316',
        'source_manifest_sha256': sha(S / 'integration/SOURCE_CLOSURE.json'),
        'scope_sha256': sha(a.scope), 'controller_sha256': sha(__file__),
        'parent_final_RESULT_sha256': sha(a.integrated / 'RESULT.json'),
        'BUILD_sha256': sha(out / 'BUILD.json'), 'INHERITED316_sha256': sha(out / 'INHERITED316.json'),
        'source_modules_recompiled': 24, 'inherited_verified_source_modules': 316,
        'scope_csv_sha256': scope_csv_hash, 'written_declaration_identities': 53,
        'distinct_scoped_theorem_names_audited': sorted(expected_theorems),
        'independent_cold340_claim': False, 'source_first_PV_claim': False,
        'seconds': time.monotonic() - started,
        'peak_child_RSS_KiB': max(r['peak_RSS_KiB'] for r in rows),
        'owned_disk_bytes': sum(p.stat().st_size for p in out.rglob('*') if p.is_file() and not p.is_symlink()),
        'observed_process_OOM_events': 0, 'axiom_audits': audits,
        'preflight_command': cli, 'preflight_stdout': preflight.stdout,
        'compiler_sha256': ctx['compiler_sha256'], 'generic_context_sha256': sha(ctx_path)})
    print('PASS_INDEPENDENT_FROZEN24_CANONICAL_APPEND_OVER_VERIFIED_FRESH316', flush=True)


if __name__ == '__main__':
    main()
