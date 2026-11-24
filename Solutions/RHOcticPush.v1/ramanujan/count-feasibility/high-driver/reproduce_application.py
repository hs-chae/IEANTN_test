#!/usr/bin/env python3
"""Fresh source-only high-input application proof, without numerical certificates.

Only pinned generic libraries are reused. This proves every successful modeled
main outputs pi(1490000000000), leaving that value symbolic. The separate full
kernel count and the external renderer/model/compiler/runtime contracts remain.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, sys, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
PORTABLE = HERE.parent/'portable'
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))

def save(path, value):
    tmp = Path(str(path)+'.pending')
    tmp.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')
    os.replace(tmp, path)

def rel(module, suffix='.lean'):
    return Path(*module.split('.')).with_suffix(suffix)

def source_plan():
    small = read(PORTABLE/'SOURCE_CLOSURE.json')
    frozen = read(HERE/'SOURCE_FREEZE.json')
    pinned = {row['path']: row['sha256'] for row in frozen['sources']}
    candidates = {}
    for row in small['modules']:
        source = PORTABLE/'source'/row['relative']
        need(sha(source) == row['source_sha256'], 'frozen portable application source')
        candidates[row['module']] = dict(module=row['module'], source=str(source),
                                        sha256=row['source_sha256'], imports=row['imports'])
    names = ['RamanujanPV.QuotientCHeapShape', 'RamanujanPV.QuotientDriverExecution',
             'RamanujanPV.QuotientDriverSuccess', 'HighDriverSource',
             'HighDriverRuntime', 'HighDriverContract']
    for mod in names:
        source = HERE/'generic'/rel(mod) if mod.startswith('RamanujanPV.') else HERE/rel(mod)
        need(sha(source) == pinned[str(source.relative_to(HERE))], 'exact application proof source')
        imports = [name for line in source.read_text().splitlines() if line.startswith('import ')
                   for name in line.split()[1:]]
        candidates[mod] = dict(module=mod, source=str(source), sha256=sha(source), imports=imports)
    ordered, seen, active = [], set(), set()
    def visit(mod):
        if mod in seen:
            return
        need(mod not in active and mod in candidates, 'complete source DAG')
        active.add(mod)
        for dep in candidates[mod]['imports']:
            if dep in candidates:
                visit(dep)
            else:
                need(dep.split('.')[0] in {'Mathlib', 'Lean', 'Init', 'Std'},
                     'unmapped application import: '+dep)
        active.remove(mod)
        seen.add(mod)
        ordered.append(candidates[mod])
    visit('HighDriverContract')
    resources = []
    for row in small['resources']:
        source = PORTABLE/'source'/row['relative']
        need(sha(source) == row['sha256'], 'original source resource')
        resources.append(dict(relative=row['relative'], source=str(source), sha256=row['sha256']))
    source = HERE/'c/verified_quotient_driver_high.c'
    need(sha(source) == pinned['c/verified_quotient_driver_high.c'], 'actual new C main')
    resources.append(dict(relative='c/'+source.name, source=str(source), sha256=sha(source)))
    return dict(modules=ordered, resources=resources,
                portable_manifest_sha256=sha(PORTABLE/'SOURCE_CLOSURE.json'),
                source_freeze_sha256=sha(HERE/'SOURCE_FREEZE.json'))

def verify(out, candidate=None):
    result = read(candidate or out/'RESULT.json')
    need(result['status'] == 'PASS_FRESH_SOURCE_HIGH_MAIN_APPLICATION_MODEL', 'complete proof result')
    need(result['script_sha256'] == sha(__file__) == sha(out/'reproduce.executed.py'), 'exact controller')
    plan = source_plan()
    need(json.dumps(result['source_plan'], sort_keys=True, allow_nan=False) ==
         json.dumps(plan, sort_keys=True, allow_nan=False), 'exact scientific source closure')
    need(len(result['build']) == len(plan['modules'])+1, 'every compiler route')
    expected = [q['module'] for q in plan['modules']]+['HighApplicationAudit']
    need([q['module'] for q in result['build']] == expected, 'ordered exact compiler identities')
    ctx = result['context']
    need(sha(ctx['compiler']) == ctx['compiler_sha256'] == result['compiler_sha256'],
         'actual pinned compiler')
    for row in result['build']:
        mod = row['module']
        need(type(row['returncode']) is int and row['returncode'] == 0, 'actual compiler status')
        need(sha(out/'source'/rel(mod)) == row['source_sha256'] and
             sha(out/'objects'/rel(mod, '.olean')) == row['object_sha256'], 'source/object association')
        command = ['/usr/bin/prlimit', '--as='+str(64 << 30), '--', '/usr/bin/time', '-v',
            '-o', str(out/'logs'/(mod+'.resources')), ctx['compiler'], '--root='+str(out/'source'),
            '-j1', str(out/'source'/rel(mod)), '-o', str(out/'objects'/rel(mod, '.olean'))]
        need(row['command'] == command, 'exact source/object/kernel compiler command')
        for suffix in ['stdout', 'stderr', 'resources']:
            need(sha(out/'logs'/(mod+'.'+suffix)) == row[suffix+'_sha256'], 'compiler log identity')
    text = (out/'logs/HighApplicationAudit.stdout').read_text()
    rows = [json.loads(line.split('HIGH_MAIN_PROOF ', 1)[1]) for line in text.splitlines()
            if 'HIGH_MAIN_PROOF {' in line]
    need(rows and all(set(q['axioms']) <= ALLOW for q in rows), 'complete source proof axiom audit')
    need(len({q['name'] for q in rows}) == len(rows), 'unique theorem identities')
    counts = re.findall(r'HIGH_MAIN_AUDIT_PASS (\d+)', text)
    need(len(counts) == 1 and int(counts[0]) == len(rows), 'complete actual theorem audit')
    need({q['name'] for q in rows} >= {
        'RHOcticPush.HighDriverContract.actual_source_model_main',
        'RHOcticPush.HighDriverContract.complete_canonical_model_run',
        'RHOcticPush.HighDriverContract.output_of_exact_count'}, 'actual final consumers')
    need(result['new_complete_source_first_PV_claim'] is False and
         result['exact_numerical_value_proved'] is False, 'explicit trust/numerical boundaries')
    need([q['module'] for q in result['dependencies']] == expected, 'every actual import probe')
    allowed = {(out/'objects'/rel(mod, '.olean')).resolve() for mod in expected}
    generic = [Path(p).resolve() for p in ctx['generic_libraries']]
    generic.append(Path(ctx['compiler']).resolve().parents[1]/'lib/lean')
    for probe in result['dependencies']:
        mod = probe['module']
        need(type(probe['returncode']) is int and probe['returncode'] == 0, 'actual import probe status')
        need(probe['command'] == [ctx['compiler'], '--root='+str(out/'source'), '--deps',
                                  str(out/'source'/rel(mod))], 'exact dependency command')
        for suffix in ['stdout', 'stderr']:
            need(sha(out/'dependencies'/(mod+'.'+suffix)) == probe[suffix+'_sha256'], 'probe hash')
        lines = (out/'dependencies'/(mod+'.stdout')).read_text().splitlines()
        need(bool(lines), 'nonempty actual dependency closure')
        for line in lines:
            path = Path(line).resolve()
            need(path in allowed or any(path.is_relative_to(g) for g in generic),
                 'foreign application object admitted')
    return result

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--out', type=Path)
    p.add_argument('--verify', type=Path)
    p.add_argument('--context', type=Path,
                   default=ROOT/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')
    a = p.parse_args()
    if a.verify:
        need(a.out is None, 'exclusive verification mode')
        print(verify(a.verify.resolve())['status'])
        return
    need(a.out is not None and not a.out.exists(), 'fresh output required')
    out, ctx, plan = a.out.resolve(), read(a.context), source_plan()
    need(sha(ctx['compiler']) == ctx['compiler_sha256'], 'pinned Lean compiler')
    for dep in ctx['generic_dependencies']:
        cp = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=dep['path'],
                            capture_output=True, text=True)
        need(cp.returncode == 0 and cp.stdout.strip() == dep['revision'],
             'pinned generic dependency revision')
        need(subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--'],
                            cwd=dep['path']).returncode == 0, 'generic tracked source drift')
    available = next(int(line.split()[1])*1024 for line in Path('/proc/meminfo').read_text().splitlines()
                     if line.startswith('MemAvailable:'))
    need(available >= 576*(1 << 30), '512GiB host reserve plus64GiB job cap')
    out.mkdir()
    for directory in ['source', 'objects', 'logs', 'dependencies']:
        (out/directory).mkdir()
    for row in plan['modules']:
        path = out/'source'/rel(row['module'])
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(Path(row['source']).read_bytes())
    for row in plan['resources']:
        path = out/'source'/row['relative']
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(Path(row['source']).read_bytes())
    mods = [row['module'] for row in plan['modules']]
    audit = 'import HighDriverContract\nimport Lean\nopen Lean Elab Command\nrun_cmd do\n'
    audit += '  let env ← getEnv\n  let mods := #['+','.join(json.dumps(x) for x in mods)+']\n'
    audit += '''  let allowed := #[`propext, `Classical.choice, `Quot.sound]
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
    (out/'source/HighApplicationAudit.lean').write_text(audit)
    (out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(out/'objects'), *ctx['generic_libraries']])
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    build = []
    dependencies = []
    start = time.monotonic()
    for mod in mods+['HighApplicationAudit']:
        source, obj = out/'source'/rel(mod), out/'objects'/rel(mod, '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        resource = out/'logs'/(mod+'.resources')
        cmd = ['/usr/bin/prlimit', '--as='+str(64 << 30), '--', '/usr/bin/time', '-v',
               '-o', str(resource), ctx['compiler'], '--root='+str(out/'source'), '-j1',
               str(source), '-o', str(obj)]
        t = time.monotonic()
        with (out/'logs'/(mod+'.stdout')).open('w') as so, \
             (out/'logs'/(mod+'.stderr')).open('w') as se:
            cp = subprocess.run(cmd, cwd=out/'source', env=env, stdout=so, stderr=se)
        row = dict(module=mod, command=cmd, returncode=cp.returncode,
                   seconds=time.monotonic()-t, source_sha256=sha(source),
                   **{suffix+'_sha256': sha(out/'logs'/(mod+'.'+suffix))
                      for suffix in ['stdout', 'stderr', 'resources']})
        if cp.returncode == 0:
            row['object_sha256'] = sha(obj)
        build.append(row)
        save(out/'BUILD.json', dict(status='RUNNING' if cp.returncode == 0 else 'FAILED', modules=build))
        need(cp.returncode == 0, 'actual compiler failure: '+mod)
        print(len(build), len(mods)+1, mod, round(row['seconds'], 2), flush=True)
    for mod in mods+['HighApplicationAudit']:
        cmd = [ctx['compiler'], '--root='+str(out/'source'), '--deps', str(out/'source'/rel(mod))]
        cp = subprocess.run(cmd, cwd=out/'source', env=env, capture_output=True, text=True)
        need(cp.returncode == 0, 'actual compiler dependency probe')
        for suffix, text in [('stdout', cp.stdout), ('stderr', cp.stderr)]:
            (out/'dependencies'/(mod+'.'+suffix)).write_text(text)
        dependencies.append(dict(module=mod, command=cmd, returncode=cp.returncode,
            **{suffix+'_sha256': sha(out/'dependencies'/(mod+'.'+suffix))
               for suffix in ['stdout', 'stderr']}))
    result = dict(status='PASS_FRESH_SOURCE_HIGH_MAIN_APPLICATION_MODEL', source_plan=plan,
        script_sha256=sha(__file__), compiler_sha256=ctx['compiler_sha256'], build=build,
        dependencies=dependencies, context=ctx,
        seconds=time.monotonic()-start, historical_application_objects_used=False,
        new_complete_source_first_PV_claim=False, exact_numerical_value_proved=False,
        mathematical_result='Every successful modeled actual newmain writes wordBytes(pi(1490000000000)); an inhabited canonical model run exists.',
        remaining='Complete numeric certificate; independent parser/renderer syntactic soundness and physical source/model/compiler/runtime/ABI/stdio/OS/hardware interpretation boundaries.')
    save(out/'CANDIDATE.json', result)
    # Final acceptance checks the entire compiler/auditor output before publish.
    verify(out, out/'CANDIDATE.json')
    os.replace(out/'CANDIDATE.json', out/'RESULT.json')
    print(result['status'], flush=True)

if __name__ == '__main__':
    main()
