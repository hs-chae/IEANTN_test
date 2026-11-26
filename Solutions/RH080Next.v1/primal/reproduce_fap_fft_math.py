#!/usr/bin/env python3
"""Rebuild the actual Fap kernel-only FFT, norm and finite ANT consumers.
This script never claims source-first PV of the numerical FFT program.
"""
import argparse, hashlib, json, os, re, shutil, subprocess, sys, time
from pathlib import Path
R = Path(__file__).resolve().parents[3]
S = R / 'Solutions/RH080Next.v1'
sys.path.insert(0, str(S / 'dual'))
from reproduce_dual import context, load, need, publish, sha
GENERIC = ('Mathlib', 'Lean', 'Init', 'Std', 'Aesop', 'Batteries', 'Qq', 'ProofWidgets')
BAD = re.compile(r'PANIC|error(?:\([^)]*\))?:|uncaught exception|failed to compile', re.I)

def validate_forest(base, c):
    plan, result = load(base / 'PLAN.json'), load(base / 'RESULT.json')
    need(not (base / 'FAILURE.json').exists(), 'Failed forest base')
    need(not (base / 'ACCEPTANCE_REVIEW.json').exists(), 'Reviewed/rejected forest base must not be reused')
    need(result['status'] == 'PASS_COMPLETE_INTEGER_FFT_TRACE_AND_LITERAL_OUTPUT_NOT_SOURCE_PV', 'Wrong forest acceptance')
    need(result['N'] == 131072 and result['stages'] == 17 and result['modules'] == 42, 'Wrong forest mathematical parameters')
    need(result['norm_numerator'] == 781796015790084776, 'Wrong original numerical output')
    candidate = plan['candidate']
    expected_input = '9f545a294f104a1baaeccbb9bf625f6338fc020af9dce9ff7bd34352630a586a'
    input_file = R/'Solutions/RH080Study.v1/ablation/followup/independent-global-chord/inputs/witness-ap.json'
    need(sha(input_file) == expected_input == candidate['input_sha256'], 'Original locked input identity mismatch')
    need(candidate['n'] == 131072 and candidate['namespace'] == 'FapForest17', 'Wrong fixed mathematical scope')
    need(candidate['norm_numerator'] == 781796015790084776, 'Wrong candidate numerator metadata')
    need(candidate['total_abs'] == 102468342420806369668447945569060309170116, 'Wrong absolute sum metadata')
    need(candidate['quad'] == 12681061983660556400000, 'Wrong locked curvature metadata')
    need(candidate['seed'] == [999999998851026827562673307794554109,-47936899603066884549003990494659], 'Wrong locked root seed metadata')
    need(sha(base/'producer.executed.py') == candidate['producer_sha256'], 'Forest producer snapshot changed')
    need(sha(base/'CANDIDATE.json') == plan['candidate_plan_sha256'], 'Candidate snapshot changed')
    need(load(base/'CANDIDATE.json') == candidate, 'Candidate identity differs from frozen plan')
    need(result['plan_sha256'] == sha(base / 'PLAN.json'), 'Forest plan changed')
    need(plan['context']['compiler_sha256'] == c['compiler_sha256'], 'Compiler mismatch')
    need(plan['context']['generic_dependencies'] == c['generic_dependencies'], 'Generic dependency mismatch')
    need(sha(base / 'driver.executed.py') == plan['driver_sha256'], 'Forest executed controller changed')
    for row in plan['sources']:
        need(Path(row['file']).name == row['file'], 'Invalid frozen source name')
        need(sha(base / 'sources' / row['file']) == row['sha256'], 'Forest frozen source changed')
    for row in load(base / 'OBJECTS.json'):
        need(Path(row['file']).name == row['file'], 'Invalid object name')
        need(sha(base / 'objects' / row['file']) == row['sha256'], 'Forest object changed')
    for receipt in base.glob('*.COMPILED.json'):
        item = load(receipt); name = item['module']
        need(item['returncode'] == 0, 'Failed forest compilation')
        for suffix in ('stdout', 'stderr', 'time'):
            path = base / (name + '.' + suffix)
            need(sha(path) == item[suffix + '_sha256'], 'Forest compilation log changed')
        text = (base / (name+'.stdout')).read_text() + '\n' + (base / (name+'.stderr')).read_text()
        need(BAD.search(text) is None, 'Forest compiler diagnostic, including exit-zero PANIC')
    need(len(list(base.glob('*.COMPILED.json'))) == 42, 'Incomplete forest compilation receipts')
    axes = load(base / 'AXIOM_AUDIT.json')
    need(axes['status'] == 'PASS' and len(axes['roots']) == 36, 'Incomplete forest axiom audit')
    need(all(set(row['axioms']) <= {'propext','Classical.choice','Quot.sound'} for row in axes['roots']), 'Unexpected forest axiom')
    return plan

def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context', type=Path, required=True)
    ap.add_argument('--run', type=Path, required=True)
    ap.add_argument('--forest-base', type=Path)
    ap.add_argument('--forest-workers', type=int, default=4)
    ap.add_argument('--memory-gib', type=int, default=128)
    ap.add_argument('--preflight-only', action='store_true')
    a = ap.parse_args()
    need(not os.path.lexists(a.run), 'Fresh run directory required')
    need(a.memory_gib in (64,128,256,300), 'Supported generous memory ceilings:64,128,256,300 GiB')
    c = context(a.context, R)
    a.run.mkdir(parents=True)
    (a.run / 'driver.executed.py').write_bytes(Path(__file__).read_bytes())
    started = time.monotonic()
    if a.forest_base is None:
        need(not a.preflight_only, 'Preflight requires an accepted forest base')
        candidate, base = a.run/'candidate', a.run/'forest'
        producer = S/'dual/produce_fft_forest_certificate.py'
        commands = [[sys.executable,str(producer),'--stages','17','--out',str(candidate)],
                    [sys.executable,str(S/'dual/reproduce_fft_forest.py'),'--context',str(a.context),
                     '--candidate',str(candidate),'--run',str(base),'--workers',str(a.forest_workers)]]
        for index, command in enumerate(commands):
            with (a.run/f'forest{index}.stdout').open('x') as out,(a.run/f'forest{index}.stderr').open('x') as err:
                p = subprocess.run(command, stdout=out, stderr=err)
            need(p.returncode == 0, 'Forest generation/reproduction failed')
    else:
        base = a.forest_base.resolve(strict=True)
    base_plan = validate_forest(base, c)
    bank, frozen, logs = a.run/'objects', a.run/'source', a.run/'logs'
    for path in [bank,frozen,logs]: path.mkdir()
    # The only reused application objects were freshly source-replayed and have
    # just passed complete source/object/log/axiom/diagnostic verification.
    for path in (base/'objects').iterdir():
        need(path.is_file() and not path.is_symlink(), 'Unexpected base artifact')
        shutil.copyfile(path, bank/path.name)
    for row in base_plan['sources']:
        if row['file'].endswith('.lean'):
            shutil.copyfile(base/'sources'/row['file'], frozen/row['file'])
    base_names = {row['file'][:-5] for row in base_plan['sources'] if row['file'].endswith('.lean')}
    roots = [S/'primal',S/'dual',S/'explicit',S/'pv/lean',R/'Solutions/RH080Study.v1/functional',
             R/'Solutions/RH080Study.v1/pv/lean',R/'Solutions/RH080Study.v1/sine',R/'Solutions/CH2.v6',
             R/'Solutions/RHOnePrimeEvolution.v1/gaussian_gap/portable/source',R]
    seen, active, rows = set(base_names), set(), []
    def visit(name):
        if name in seen or any(name==g or name.startswith(g+'.') for g in GENERIC): return
        need(name not in active, 'Import cycle:'+name); active.add(name)
        found = next((p for root in roots if (p:=root.joinpath(*name.split('.')).with_suffix('.lean')).is_file()),None)
        need(found is not None, 'Missing application source:'+name)
        need(found.resolve().is_relative_to(R), 'Application source outside repository')
        imports = [v for line in found.read_text().splitlines() if line.startswith('import ')
                   for v in line[7:].split('--',1)[0].split()]
        for dep in imports: visit(dep)
        target = frozen.joinpath(*name.split('.')).with_suffix('.lean');target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(found.read_bytes())
        rows.append(dict(module=name,origin=str(found),snapshot=str(target),source_sha256=sha(found),imports=imports))
        active.remove(name);seen.add(name)
    visit('FapFFTKernelAudit')
    plan = dict(status='PREFLIGHT_ONLY' if a.preflight_only else 'VALIDATED_SOURCE_COLD_FOREST_AND_FULL_ANT_CLOSURE',
                forest_base=str(base),forest_result_sha256=sha(base/'RESULT.json'),forest_plan_sha256=sha(base/'PLAN.json'),
                forest_modules=42,additional_sources=rows,controller_sha256=sha(Path(__file__)),
                context_sha256=sha(a.context),generic=c['generic_dependencies'],memory_ceiling_gib=a.memory_gib,
                command=sys.argv,historical_or_unvalidated_application_fallback=False,
                numerical_status='KERNEL_ONLY_NOT_SOURCE_PV')
    publish(a.run/'PLAN.json',plan)
    if a.preflight_only:
        print(json.dumps(dict(status='PREFLIGHT_ONLY',forest_modules=42,additional_modules=len(rows))))
        return
    env = dict(os.environ,LEAN_PATH=str(bank)+':'+c['generic_lean_path'])
    compiled=[]
    for row in rows:
        name=row['module'];target=bank.joinpath(*name.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        tag=name.replace('.','_');out,err,tm=(logs/(tag+s) for s in ['.stdout','.stderr','.time'])
        command=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as='+str(a.memory_gib*2**30),
                 '--stack='+str(256*2**20),'--',c['compiler'],'-j1','--root='+str(frozen),'-o',str(target),row['snapshot']]
        t=time.monotonic()
        with out.open('x') as o,err.open('x') as e: p=subprocess.run(command,cwd=frozen,env=env,stdout=o,stderr=e)
        text=out.read_text()+'\n'+err.read_text()
        if p.returncode != 0 or BAD.search(text) is not None:
            publish(a.run/'FAILURE.json',dict(status='NO_ACCEPTANCE',module=name,exitcode=p.returncode,
                    oom_or_sigkill=int(p.returncode in (-9,137) or 'Command terminated by signal 9' in tm.read_text()),
                    stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(tm),completed=compiled))
            raise ValueError('Compiler failure/diagnostic:'+name)
        need(target.is_file(),'Missing proof object:'+name)
        artifacts=[dict(path=str(q.relative_to(bank)),sha256=sha(q),bytes=q.stat().st_size)
                   for q in sorted(target.parent.glob(target.name+'*')) if q.is_file()]
        item=dict(module=name,exitcode=p.returncode,seconds=time.monotonic()-t,command=command,
                  object_sha256=sha(target),object_artifacts=artifacts,stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(tm))
        publish(a.run/(tag+'.COMPILED.json'),item);compiled.append(item)
    validate_forest(base,c)
    for row in rows:
        need(sha(Path(row['origin']))==row['source_sha256']==sha(Path(row['snapshot'])),'Application source changed')
    need(sha(Path(__file__))==plan['controller_sha256'],'Controller changed')
    audit=(logs/'FapFFTKernelAudit.stdout').read_text()
    need('FAP_KERNEL_ANT_AUDIT_PASS roots=14 numerical_norm_premises=0 FFT_status=KERNEL_ONLY_NOT_PV' in audit,'Missing final ANT gate')
    peak=0
    for tm in logs.glob('*.time'):
        m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tm.read_text())
        if m: peak=max(peak,int(m.group(1)))
    objects=[dict(path=str(p.relative_to(bank)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(bank.rglob('*')) if p.is_file()]
    publish(a.run/'OBJECTS.json',objects)
    publish(a.run/'RESULT.json',dict(status='PASS_FAP_FFT_NORM_AND_FULL_FINITE_ANT_KERNEL_ONLY',
            forest_modules=42,additional_modules=len(rows),audited_roots=14,seconds=time.monotonic()-started,
            max_additional_process_RSS_KiB=peak,base_max_process_RSS_KiB=load(base/'RESULT.json')['max_individual_RSS_KiB'],
            disk_bytes=sum(p.stat().st_size for p in a.run.rglob('*') if p.is_file()),oom_or_sigkill_events=0,
            numerical_norm_premises=0,source_first_FFT_PV_complete=False,formal_analytic_inputs=['BRNormFive','BRStrip','CMSGuinandWeil','DLMFDigamma','CMSZeroPartialSummation','CMSZeroCounting','DLMFEta','MontgomeryVaughan','RH','HistoricalFiniteGap']))
    print((a.run/'RESULT.json').read_text())

if __name__=='__main__': main()
