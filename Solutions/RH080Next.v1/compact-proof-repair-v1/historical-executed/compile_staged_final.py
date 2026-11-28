#!/usr/bin/env python3
"""Private source-associated staged proof test; all mathematical leaves are pinned.
Requires an owned physical cgroup, no swap, unlimited virtual AS, THP0 and actual CPU placement.
Never accepts a failed child, forbidden diagnostic, missing object, changed source, or non-Std3 audit.
"""
import argparse, json, os, re, shutil, signal, subprocess, sys, time
from pathlib import Path
D = Path('/data/ivy-rh080-next-20261125')
S = D / 'network/Solutions/RH080Next.v1'
sys.path.insert(0, str(S / 'dual'))
import resume_fft_dag_source_cold as original
from reproduce_dual import context, need, sha, load, publish

GIB = 2**30
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
BAD = re.compile(r'PANIC|error(?:\([^)]*\))?:|fatal error|sorryAx|native_decide|Lean\.ofReduceBool', re.I)
SOURCE_BAD = re.compile(r'^\s*(?:axiom|opaque|sorry|admit)\b|\bnative_decide\b', re.M)
BASELINE_LINT = ['Unused tactic linter: `all_goals decide +kernel` does nothing',
                 'this tactic is never executed']


def events(cg):
    return dict((k, int(v)) for k, v in
                (line.split() for line in (cg / 'memory.events').read_text().splitlines()))


def memory_available():
    return next(int(line.split()[1]) * 1024 for line in Path('/proc/meminfo').read_text().splitlines()
                if line.startswith('MemAvailable:'))


def usage():
    p = subprocess.run(['/usr/bin/du', '-s', '-x', '-B1', str(D)],
                       capture_output=True, text=True)
    need(p.returncode == 0, 'Complete scratch usage measurement required')
    return int(p.stdout.split()[0])


def atomic_live(path, value):
    temporary = path.with_suffix('.pending')
    temporary.write_text(json.dumps(value, allow_nan=False) + '\n')
    temporary.replace(path)


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--assembly', type=Path, required=True)
    ap.add_argument('--run', type=Path, required=True)
    ap.add_argument('--physical-gib', type=int, choices=[64, 300], required=True)
    ap.add_argument('--prepare-only', action='store_true')
    a = ap.parse_args()
    need(not os.path.lexists(a.run), 'Fresh private proof run required')
    assembly = load(a.assembly / 'ASSEMBLY.json')
    expected_assemblies = {13: 'fecf565c9b123ec0b2175d578e22bd54629491164d9273884b45c2231568f018',
                           24: '90ee5f088699fe261859ac3fa8296e1a07aa7477a959b60ad2bcc4b2210d0ce6'}
    stage = assembly['stage']
    need(stage in expected_assemblies and sha(a.assembly / 'ASSEMBLY.json') ==
         expected_assemblies[stage], 'Reviewed exact proof-only assembly required')
    need(type(stage) is int and stage in [13, 24], 'Pinned stage required')
    need((stage == 13 and a.physical_gib == 64) or
         (stage == 24 and a.physical_gib == 300), 'Matched actual stage physical policy required')
    need(assembly['same_public_FQ_names_and_type_headers'] is True and
         assembly['all_nonshape_bodies_byte_unchanged'] is True and
         assembly['original_typed_audit_byte_unchanged'] is True, 'Exact original claims required')
    bank = Path(assembly['original_bank'])
    base = load(bank / 'PLAN.json')
    need(sha(bank / 'PLAN.json') == assembly['original_plan_sha256'], 'Original bank changed')
    for key in ['Final', 'ClaimAudit']:
        need(sha(Path(assembly[f'original_{key}_source'])) ==
             assembly[f'original_{key}_sha256'], 'Original source changed')
    modules = assembly['modules']
    need(len(modules) == stage + 8, 'Unexpected bounded stage count')
    for row in modules:
        p = a.assembly / row['file']
        need(sha(p) == row['sha256'] and not SOURCE_BAD.search(p.read_text()),
             'Generated proof source changed or forbidden construct')
    audit_name = f'W4D{stage}ClaimAudit'
    need(sha(a.assembly / (audit_name + '.lean')) ==
         assembly['original_ClaimAudit_sha256'], 'Original typed consumer not byte identical')
    membership = [line.split('::', 1)[1] for line in Path('/proc/self/cgroup').read_text().splitlines()
                  if line.startswith('0::')]
    need(len(membership) == 1 and membership[0].endswith('.service'), 'Owned cgroup required')
    cg = Path('/sys/fs/cgroup') / membership[0].lstrip('/')
    limit = a.physical_gib * GIB
    need((cg / 'memory.max').read_text().strip() == str(limit) and
         (cg / 'memory.swap.max').read_text().strip() == '0', 'Actual physical cap/noSwap required')
    before = events(cg)
    mem = memory_available()
    need(mem >= ((1024 if stage == 24 else 320) * GIB), 'Fresh real RAM admission failed')
    free_disk = shutil.disk_usage(D).free
    need(free_disk >= 1024 * GIB, 'Independent fresh disk admission failed')
    used = usage()
    need(used <= 290 * GIB, 'Campaign scratch admission reserve failed')
    status = Path('/proc/self/status').read_text()
    need(re.search(r'^THP_enabled:\s*0$', status, re.M), 'Whole coordinator must inherit THP0')
    need(set(os.sched_getaffinity(0)) == {96, 97, 98, 99}, 'Actual coordinator CPU96-99 required')
    cp = Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json')
    c = context(cp, original.R)
    rows = {r['module']: r for r in base['sources']}
    accepted = []
    seen = set()

    def visit(name):
        if name in seen or name.split('.')[0] in original.GENERIC:
            return
        need(name not in [f'W4D{stage}Final', audit_name], 'Original incomplete Final cannot be reused')
        need(name in rows, 'Missing exact accepted leaf ' + name)
        seen.add(name)
        row = rows[name]
        for child in row['imports']:
            visit(child)
        route = base.get('routes', {}).get(name)
        logical = Path(route['logical_compile_origin']) if route else bank
        rec = original.receipt(bank, logical, row, c['compiler'], True)
        accepted.append(dict(module=name, source=str(bank / 'sources' / row['file']),
            source_sha256=row['sha256'], object=str(bank / 'objects' /
            (name.replace('.', '/') + '.olean')), object_sha256=rec['object_sha256'],
            compiler_receipt=str(bank / (name + '.COMPILED.json')),
            receipt_sha256=sha(bank / (name + '.COMPILED.json')),
            logical_compile_origin=str(logical)))

    for child in rows[f'W4D{stage}Final']['imports']:
        visit(child)
    need(len(accepted) == (118 if stage == 13 else 1031), 'Exact numerical leaf closure required')
    a.run.mkdir()
    objects = a.run / 'objects'
    objects.mkdir()
    for row in accepted:
        target = objects / (row['module'].replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        os.link(row['object'], target)
    pinned = [dict(path=str(p), sha256=sha(p)) for p in
              [Path(__file__), a.assembly / 'ASSEMBLY.json', cp] +
              [a.assembly / row['file'] for row in modules]]
    plan = dict(status='PRIVATE_STAGED_SOURCE_ASSOCIATED_PROOF_ONLY_TEST_NOT_NETWORK_ACCEPTANCE',
                stage=stage, modules=modules, inherited_closed_leaves=accepted,
                source_pins=pinned, compiler_sha256=c['compiler_sha256'],
                generic_dependencies=c['generic_dependencies'], context_sha256=sha(cp),
                physical_limit_bytes=limit, memory_events_before=before, cgroup=str(cg),
                virtual_AS='unlimited', whole_coordinator_THP_enabled=0,
                actual_coordinator_affinity=sorted(os.sched_getaffinity(0)),
                available_RAM_before_bytes=mem, independent_free_disk_before_bytes=free_disk,
                campaign_scratch_before_bytes=used, original_assembly=assembly,
                reused_leaf_only_object_root=True, original_Final_or_audit_fallback=False)
    publish(a.run / 'PLAN.json', plan)
    if a.prepare_only:
        print('PREPARED ONLY NO PROOF ACCEPTANCE', flush=True)
        return
    env = dict(os.environ, LEAN_PATH=str(objects) + ':' + c['generic_lean_path'])
    started = time.monotonic()
    records = []
    current_child = None
    stopping = False

    def stop(signum, frame):
        nonlocal stopping
        stopping = True
        if current_child is not None and current_child.poll() is None:
            os.killpg(current_child.pid, signal.SIGTERM)

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    try:
        for row in modules:
            need(not stopping, 'Intentional controller stop')
            name = row['module']
            source = a.assembly / row['file']
            obj = objects / (name + '.olean')
            tm = a.run / (name + '.time')
            outpath = a.run / (name + '.stdout')
            errpath = a.run / (name + '.stderr')
            command = ['/usr/bin/time', '-v', '-o', str(tm), 'prlimit', '--as=unlimited',
                       '--stack=' + str(256 * 2**20), '--', c['compiler'], '-j1',
                       '--root=' + str(a.assembly), '-o', str(obj), str(source)]
            tick = time.monotonic()
            peak_charge = 0
            child_policy = None
            guard_failure = None
            last_scratch_check = time.monotonic()
            sampled_campaign_scratch_max = used
            with outpath.open('xb') as out, errpath.open('xb') as err:
                current_child = subprocess.Popen(command, env=env, stdout=out, stderr=err,
                                                 start_new_session=True)
                while current_child.poll() is None:
                    now_mem = memory_available()
                    charge = int((cg / 'memory.current').read_text())
                    peak_charge = max(peak_charge, charge)
                    children = Path(f'/proc/{current_child.pid}/task/{current_child.pid}/children')
                    if child_policy is None and children.exists():
                        ids = children.read_text().split()
                        if ids:
                            pid = int(ids[0])
                            try:
                                st = Path(f'/proc/{pid}/status').read_text()
                                if re.search(r'^Name:\s*lean$', st, re.M):
                                    child_policy = dict(pid=pid,
                                        THP_enabled=int(re.search(r'^THP_enabled:\s*(\d+)', st, re.M)[1]),
                                        affinity=sorted(os.sched_getaffinity(pid)),
                                        limits=Path(f'/proc/{pid}/limits').read_text())
                            except (FileNotFoundError, ProcessLookupError):
                                pass
                    live = dict(status='ACTIVE_NOT_ACCEPTED', module=name,
                                child_elapsed_seconds=time.monotonic() - tick,
                                cgroup_memory_current_bytes=charge,
                                sampled_cgroup_charge_max_bytes=peak_charge,
                                actual_events=events(cg), host_available_RAM_bytes=now_mem,
                                actual_child_policy=child_policy)
                    atomic_live(a.run / 'LIVE.json', live)
                    if time.monotonic() - last_scratch_check >= 15:
                        scratch_now = usage()
                        sampled_campaign_scratch_max = max(sampled_campaign_scratch_max, scratch_now)
                        last_scratch_check = time.monotonic()
                        if scratch_now > 300 * GIB:
                            guard_failure = 'Runtime campaign scratch limit failed'
                            os.killpg(current_child.pid, signal.SIGTERM)
                            break
                    if now_mem < 256 * GIB or shutil.disk_usage(D).free < 256 * GIB:
                        guard_failure = 'Runtime host RAM/disk reserve failed'
                        os.killpg(current_child.pid, signal.SIGTERM)
                        break
                    if stopping:
                        break
                    time.sleep(0.5)
                rc = current_child.wait()
            timing = tm.read_text() if tm.exists() else ''
            peak = re.findall(r'Maximum resident set size \(kbytes\):\s*(\d+)', timing)
            record = dict(module=name, command=command, returncode=rc,
                          seconds=time.monotonic() - tick, source_sha256=sha(source),
                          object_sha256=sha(obj) if obj.is_file() else None,
                          stdout_sha256=sha(outpath), stderr_sha256=sha(errpath),
                          time_sha256=sha(tm) if tm.exists() else None,
                          peak_RSS_KiB=int(peak[0]) if len(peak) == 1 else None,
                          sampled_cgroup_charge_max_bytes=peak_charge,
                          actual_child_policy=child_policy,
                          sampled_campaign_scratch_max_bytes=sampled_campaign_scratch_max,
                          memory_events_after=events(cg), guard_failure=guard_failure)
            publish(a.run / (name + '.COMPILED.json'), record)
            records.append(record)
            need(rc == 0 and guard_failure is None and not stopping, 'Failed compiler ' + name)
            need(record['object_sha256'] is not None and len(peak) == 1 and
                 int(peak[0]) > 0 and not re.search(r'Command terminated by signal', timing) and
                 re.search(r'Exit status:\s*0\s*$', timing), 'Incomplete GNUtime/object ' + name)
            stdout, stderr = outpath.read_text(), errpath.read_text()
            need(not stderr and not BAD.search(stdout), 'Forbidden compiler diagnostic ' + name)
            lint = re.findall(r'warning: ([^\n]*)', stdout)
            expected_lint = BASELINE_LINT if name == f'W4D{stage}FinalTotal' else []
            need(lint == [] or lint == expected_lint, 'Unexpected warning ' + name)
            if child_policy is not None:
                need(child_policy['THP_enabled'] == 0 and
                     child_policy['affinity'] == [96, 97, 98, 99] and
                     re.search(r'^Max address space\s+unlimited\s+unlimited',
                               child_policy['limits'], re.M), 'Actual compiler resource policy differs')
            if name.endswith('ImportsProbe'):
                need(f'STAGED_IMPORT_ONLY_PASS W4DAG{stage} original_import_union' in stdout,
                     'No completed actual import-union marker')
            for declaration in row['public_declarations']:
                if name != audit_name:
                    need('STAGED_BEGIN ' + declaration in stdout and
                         'STAGED_END ' + declaration in stdout, 'Incomplete declaration marker')
            if name == audit_name:
                axes = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", stdout)
                noaxes = re.findall(r"'([^']+)' does not depend on any axioms", stdout)
                expected = row['public_declarations']
                found = [name for name, names in axes] + noaxes
                need(len(found) == stage + 5 and set(found) == set(expected) and
                     len(set(found)) == len(found), 'Missing/duplicate original exact typed audits')
                for root, names in axes:
                    need(all(x.strip() in ALLOWED for x in names.split(',') if x.strip()),
                         'Nonstandard execution axiom in ' + root)
                record['actual_original_typed_root_axioms'] = dict(
                    [(root, [x.strip() for x in names.split(',') if x.strip()])
                     for root, names in axes] + [(root, []) for root in noaxes])
            print('COMPILED', name, round(record['seconds'], 3), record['peak_RSS_KiB'], flush=True)
        after = events(cg)
        need(after['oom'] == before['oom'] and after['oom_kill'] == before['oom_kill'],
             'Actual OOM event prevents acceptance')
        for row in pinned:
            need(sha(Path(row['path'])) == row['sha256'], 'Executed source/context changed')
        for row in accepted:
            need(sha(Path(row['source'])) == row['source_sha256'] and
                 sha(Path(row['object'])) == row['object_sha256'] and
                 sha(Path(row['compiler_receipt'])) == row['receipt_sha256'],
                 'Accepted leaf evidence changed')
        need(sha(bank / 'PLAN.json') == assembly['original_plan_sha256'], 'Original plan changed')
        publish(a.run / 'RESULT.json', dict(
            status='PASS_PRIVATE_STAGED_IDENTICAL_PUBLIC_STATEMENTS_AND_ORIGINAL_TYPED_AUDIT',
            stage=stage, modules=len(records), records=records,
            seconds=time.monotonic() - started, original_typed_roots=stage + 5,
            inherited_source_associated_numerical_leaves=len(accepted),
            exact_original_nonshape_bodies=True, same_original_public_FQ_names_and_types=True,
            original_ClaimAudit_byte_identical=True, new_unverified_axioms_sorry_native=False,
            source_cold=False, full_C_source_first_PV_claimed=False,
            memory_events_before=before, memory_events_after=after,
            max_individual_RSS_KiB=max(r['peak_RSS_KiB'] for r in records),
            physical_limit_bytes=limit, sampled_aggregate_charge_is_not_GNU_peak=True,
            campaign_scratch_after_bytes=usage(), plan_sha256=sha(a.run / 'PLAN.json')))
        print('PASS PRIVATE STAGED ORIGINAL CLAIMS', stage, flush=True)
    except BaseException as error:
        if current_child is not None and current_child.poll() is None:
            os.killpg(current_child.pid, signal.SIGTERM)
            current_child.wait()
        publish(a.run / 'FAILURE.json', dict(
            status='NO_ACCEPTANCE_PRIVATE_STAGED_PROOF', error=str(error),
            completed_or_failed_records=len(records), seconds=time.monotonic() - started,
            memory_events_before=before, memory_events_after=events(cg),
            physical_limit_bytes=limit, plan_sha256=sha(a.run / 'PLAN.json')))
        raise


if __name__ == '__main__':
    main()
