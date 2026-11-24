#!/usr/bin/env python3
"""Compile independent final-consumer audit and adversarial mathematical controls.
--objects must be the accepted fresh application object directory for final use.
Development --bank overlays are explicitly labelled, never called a fresh replay.
"""
import argparse, hashlib, json, os, re, subprocess, time
from pathlib import Path

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic_json(path,value):
    temporary=path.with_name(path.name+'.tmp')
    if temporary.exists():raise SystemExit('Unexpected existing atomic receipt temporary')
    with temporary.open('x') as stream:
        json.dump(value,stream,indent=2);stream.write('\n');stream.flush();os.fsync(stream.fileno())
    os.replace(temporary,path)
    directory=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY)
    try:os.fsync(directory)
    finally:os.close(directory)
def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--repository',type=Path,required=True)
    p.add_argument('--run',type=Path,required=True)
    p.add_argument('--objects',type=Path)
    p.add_argument('--bank',type=Path,action='append',default=[])
    a=p.parse_args(); repo=a.repository.resolve(strict=True); run=a.run.resolve()
    if run.exists(): raise SystemExit('Fresh run required')
    if bool(a.objects)==bool(a.bank): raise SystemExit('Choose final objects OR development banks')
    study=repo/'Solutions/RHOnePrimeEvolution.v1'
    ctx=json.loads((study/'scripts/LOCAL_CONTEXT.json').read_text())
    source,objs,logs=[run/n for n in ('source','objects','logs')]
    for d in (source,objs,logs):d.mkdir(parents=True)
    (run/'run_audit.executed.py').write_bytes(Path(__file__).read_bytes())
    (run/'LOCAL_CONTEXT.executed.json').write_bytes((study/'scripts/LOCAL_CONTEXT.json').read_bytes())
    env=os.environ.copy()
    if a.objects:
        bank=a.objects.resolve(strict=True)
        if not (bank.parent/'EXECUTION.json').exists():raise SystemExit('Final compilation receipt required')
        receipt=json.loads((bank.parent/'EXECUTION.json').read_text())
        if receipt['status']!='PASS_FRESH_TRANSITIVE_COMPILATION':raise SystemExit('Final source closure must pass first')
        plan_path=bank.parent/'PLAN.json';plan=json.loads(plan_path.read_text())
        if sha(plan_path)!=receipt['PLAN_sha256']:raise SystemExit('Fresh PLAN receipt hash mismatch')
        if receipt['compiled_modules']!=receipt['required_modules'] or receipt['required_modules']!=len(plan['modules']):
            raise SystemExit('Incomplete final source compilation')
        built={r['module']:r for r in receipt['builds']}
        planned={r['module']:r for r in plan['modules']}
        if len(built)!=len(receipt['builds']) or set(built)!=set(planned):raise SystemExit('Final module identity mismatch')
        for module,row in planned.items():
            if sha(Path(row['executed']))!=row['source_sha256']:raise SystemExit('Frozen source hash mismatch '+module)
            if sha(Path(row['origin']))!=row['source_sha256']:raise SystemExit('Current/frozen source differs '+module)
            if built[module]['returncode']!=0:raise SystemExit('Failed final module '+module)
            if sha(bank/(module.replace('.','/')+'.olean'))!=built[module]['object_sha256']:
                raise SystemExit('Final object hash mismatch '+module)
        if sha(Path(ctx['compiler']))!=plan['compiler_sha256']:raise SystemExit('Different compiler from final closure')
        mode='FRESH_CLOSURE_CONSUMER_AUDIT'
        search=str(bank)
    else:
        mode='DEVELOPMENT_REUSED_OBJECT_AUDIT'
        for bank in a.bank:
            bank=bank.resolve(strict=True)
            for original in bank.rglob('*'):
                if original.is_file():
                    out=objs/original.relative_to(bank);out.parent.mkdir(parents=True,exist_ok=True)
                    if out.is_symlink() or out.is_file():out.unlink()
                    out.symlink_to(original.resolve(strict=True))
        search=str(objs)
    env['LEAN_PATH']=':'.join([str(objs),search,ctx['mathlib_lean_path']])
    rows=[]
    def compile_one(module,content,expected):
        src=source/(module+'.lean'); src.write_text(content)
        out=objs/(module+'.olean')
        for suffix in ('.olean','.olean.private','.olean.server','.ilean'):
            path=objs/(module+suffix)
            if path.is_symlink() or path.is_file():path.unlink()
        cmd=['/usr/bin/prlimit','--as=68719476736','--','/usr/bin/time','-v',ctx['compiler'],'--root='+str(source),'-j2','-o',str(out),str(src)]
        start=time.monotonic()
        with (logs/(module+'.stdout')).open('wb') as stdout,(logs/(module+'.stderr')).open('wb') as stderr:
            proc=subprocess.run(cmd,env=env,stdout=stdout,stderr=stderr)
        err=(logs/(module+'.stderr')).read_text();m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',err)
        okay=proc.returncode==0 if expected=='accept' else proc.returncode!=0
        text=(logs/(module+'.stdout')).read_text()
        if expected=='reject' and 'error:' not in text:okay=False
        row=dict(module=module,expected=expected,returncode=proc.returncode,accepted_control=okay,
          source_sha256=sha(src),stdout_sha256=sha(logs/(module+'.stdout')),stderr_sha256=sha(logs/(module+'.stderr')),
          seconds=time.monotonic()-start,peak_child_RSS_KiB=int(m[1]) if m else None,command=cmd)
        rows.append(row)
        (run/'PROGRESS.json').write_text(json.dumps(rows,indent=2)+'\n')
        if not okay:raise SystemExit('Unexpected audit outcome '+module+'; see '+str(logs))
    if not a.objects:
        for mod,path in [('PowerPopulationSolution','Solutions/PrimePowerPopulation.v1/Solution.lean'),('GoldbachV3Solution','Solutions/Goldbach.v3/Solution.lean'),('PrimeQuantileV4Solution','Solutions/PrimeQuantile.v4/Solution.lean')]:
            compile_one(mod,(repo/path).read_text(),'accept')
    audit=study/'integration_review/FinalConsumerAudit.lean'
    compile_one('FinalConsumerAudit',audit.read_text(),'accept')
    if 'INDEPENDENT_CANONICAL_AUDIT_PASS 25' not in (logs/'FinalConsumerAudit.stdout').read_text():
        raise SystemExit('Missing complete 25-root compiler audit marker')
    prefix='import OnePrimeNetwork\nopen Real Set IEANTN.RHOnePrimeEvolution\n'
    controls={
      'RejectChangedCoefficient': 'example : RHOnePrimeEvolution.v1.late_open_08768 = (∀ x : ℝ, exp 44 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(877/1000)*sqrt x*log x) := rfl\n',
      'RejectEarlierOnset': 'example : RHOnePrimeEvolution.v1.late_open_08768 = (∀ x : ℝ, exp 43 ≤ x → hasPrimeOpen x (x+(548/625)*sqrt x*log x)) := rfl\n',
      'RejectClosedUpperEndpoint': 'example : RHOnePrimeEvolution.v1.late_open_08768 = (∀ x : ℝ, exp 44 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ x+(548/625)*sqrt x*log x) := rfl\n',
      'RejectExpandedFiniteCeiling': 'example : PrimeGapTable.v1.gaps = (∀ p q : ℕ, p.Prime → q.Prime → p < q → q < 2^65 → (∀ r : ℕ, p < r → r < q → ¬r.Prime) → q-p ≤ 1550) := rfl\n',
      'RejectRemovedNumericNode': 'example : CMSCosineInput.v1.obstruction → RH.v1.hypothesis → RHOnePrimeEvolution.v1.late_open_08768 := RHOnePrimeEvolution.v1.challenge_late_open_08768\n',
      'RejectRemovedSourceInput': 'example : RH.v1.hypothesis → RHOnePrimeEvolution.v1.kernel_ratio_lower → RHOnePrimeEvolution.v1.late_open_08768 := RHOnePrimeEvolution.v1.challenge_late_open_08768\n'}
    for mod,body in controls.items():compile_one(mod,prefix+body,'reject')
    result=dict(status='PASS_INDEPENDENT_EXACT_TYPE_AXIOM_VALUE_AUDIT',mode=mode,root_count=25,headline_count=24,
       negative_mathematical_controls=len(controls),rows=rows,objects=str(a.objects.resolve()) if a.objects else None,
       banks=[str(b.resolve()) for b in a.bank],audit_source_sha256=sha(audit),compiler=ctx['compiler'],
       compiler_sha256=sha(Path(ctx['compiler'])),mathlib_commit=ctx['mathlib_commit'],
       controller_sha256=sha(run/'run_audit.executed.py'),context_sha256=sha(run/'LOCAL_CONTEXT.executed.json'),
       generic_dependency_versions=ctx['generic_dependency_versions'],lean_path=env['LEAN_PATH'],
       caveat='Conditional theorem proof audit; external source predicates remain hypotheses. Not source-first PV. RSS is per-child reported maximum; disk is final allocated bytes.')
    result['owned_final_allocated_disk_bytes']=sum(p.stat().st_blocks*512 for p in run.rglob('*') if p.is_file() and not p.is_symlink())
    atomic_json(run/'RESULT.json',result)
    print(json.dumps({k:result[k] for k in ('status','mode','root_count','headline_count','negative_mathematical_controls')}))
if __name__=='__main__':main()
