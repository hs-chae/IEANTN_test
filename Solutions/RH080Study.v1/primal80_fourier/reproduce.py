#!/usr/bin/env python3
"""Fresh source replay of the new degree80 true Fourier adapter.

Only pinned Mathlib libraries are cached providers. Generic LeanCert sources,
old generic Gaussian proofs are copied without modification and rebuilt; the
new G40 source/functions and coefficient arithmetic are rebuilt. No old actual
Fourier witness theorem or numerical cell certificate is used.
"""
import argparse, hashlib, json, os, re, subprocess, time
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
def need(ok,message):
    if not ok:raise RuntimeError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--context',type=Path,default=Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json'))
    parser.add_argument('--lean-cert-source',type=Path,default=Path('/data/ivy-rh-080-20261125/baseline/gaussian53-v1/run/compile/source'))
    args=parser.parse_args();out=args.out.resolve()
    need(not out.exists(),'Fresh output directory required')
    controller_sha256=sha(Path(__file__))
    context_sha256=sha(args.context)
    context=json.loads(args.context.read_text());inputs=json.loads((HERE/'INPUTS.json').read_text())
    pins=json.loads((HERE/'DEPENDENCY_PINS.json').read_text())
    compiler=Path(context['compiler'])
    need(sha(compiler)==context['compiler_sha256']==pins['compiler_sha256'],'Compiler identity differs')
    need(subprocess.check_output([str(compiler),'--version'],text=True).strip()==context['compiler_version']==pins['compiler_version'],'Compiler version differs')
    need(context['generic_dependencies']==pins['generic_dependencies'],'Generic dependency pins differ')
    generic_paths=context['generic_lean_path'].split(':')
    need(len(generic_paths)==len(context['generic_dependencies']),'Generic path count differs')
    for path,dep in zip(generic_paths,context['generic_dependencies']):
        lib=Path(path);pkg=lib.parents[3]
        need(pkg.name==dep['name'],'Generic path order differs')
        need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=pkg,text=True).strip()==dep['revision'],'Generic source revision differs')
        need(not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=pkg,text=True),'Generic tracked source dirty')
    need(sha(HERE/'Primal80CoefficientTransform.lean')==inputs['generated_sha256'],'Generated transform differs')
    # Paths in INPUTS are relative to the repository, by generator design.
    for item in inputs['source_inputs']:
        need(sha(REPO/item['path'])==item['sha256'],'Frozen coefficient input differs')
    functions=REPO/'Solutions/RH080Study.v1/functional/primal40/G40Functions.lean'
    need(sha(functions)=='0f35f4c46951bf09bb267a8c4aeeb64ef2b9dfa2bd96f5d02b442baef9ad2a1a','Frozen actual functions differ')
    available=int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024
    need(available>=256*2**30,'Host256GiB reserve unavailable')
    seen=set();order=[]
    roots=[HERE,REPO/'Solutions/RH080Study.v1/functional/primal40',REPO/'Solutions/RHOnePrimeEvolution.v1/gaussian_fourier',REPO/'Solutions/RHOnePrimeEvolution.v1/gaussian_kernel',args.lean_cert_source]
    def visit(module):
        if module.startswith(('Mathlib','Lean.','Std.','Init.')) or module in ('Lean','Std','Init'):return
        if module in seen:return
        seen.add(module)
        candidates=[p/(module.replace('.','/')+'.lean') for p in roots]
        source=next((p for p in candidates if p.is_file()),None)
        need(source is not None,'Missing local source '+module)
        for line in source.read_text().splitlines():
            if line.startswith('import '):
                for dependency in line[7:].split('--',1)[0].split():visit(dependency)
        order.append((module,source))
    visit('Primal80FourierAudit')
    out.mkdir(parents=True);src=out/'source';obj=out/'objects';logs=out/'logs'
    for p in (src,obj,logs):p.mkdir()
    rows=[]
    for module,source in order:
        target=src/(module.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(source.read_bytes())
        rows.append(dict(module=module,source=str(source),source_sha256=sha(source)))
    plan=dict(status='FROZEN_SOURCE_CLOSURE',compiler=str(compiler),compiler_sha256=sha(compiler),modules=rows,generic_path=context['generic_lean_path'],lean_cert_source_path=str(args.lean_cert_source),lean_cert_objects_rebuilt=True,application_cache_reused=False,per_process_address_space_bytes=64*2**30,available_host_reserve_bytes=256*2**30,controller_sha256=controller_sha256,context_sha256=context_sha256,input_manifest_sha256=sha(HERE/'INPUTS.json'),dependency_pins_sha256=sha(HERE/'DEPENDENCY_PINS.json'))
    (out/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
    (out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
    env=os.environ.copy();env['LEAN_PATH']=str(obj)+':'+context['generic_lean_path']
    started=time.monotonic();results=[]
    for row in rows:
        module=row['module'];source=src/(module.replace('.','/')+'.lean');target=obj/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
        command=['/usr/bin/prlimit','--as='+str(64*2**30),'--','/usr/bin/time','-v',str(compiler),'-j2','--root='+str(src),'-o',str(target),str(source)]
        tick=time.monotonic()
        with (logs/(module+'.stdout')).open('wb') as stdout,(logs/(module+'.stderr')).open('wb') as stderr:
            result=subprocess.run(command,env=env,stdout=stdout,stderr=stderr)
        record=dict(module=module,returncode=result.returncode,elapsed_seconds=time.monotonic()-tick,command=command,object_sha256=sha(target) if target.exists() else None)
        results.append(record);(out/'PROGRESS.json').write_text(json.dumps(record)+'\n')
        if result.returncode:
            (out/'FAILED.json').write_text(json.dumps(record,indent=2)+'\n')
            print((logs/(module+'.stdout')).read_text()[-5000:]);raise SystemExit(result.returncode)
        need(sha(Path(row['source']))==row['source_sha256'],'Source changed during replay')
        print(module,'PASS',flush=True)
    for row in rows:need(sha(Path(row['source']))==row['source_sha256'],'Source changed after replay')
    need(sha(Path(__file__))==controller_sha256,'Controller changed during replay')
    need(sha(args.context)==context_sha256,'Generic context changed during replay')
    need(sha(HERE/'INPUTS.json')==plan['input_manifest_sha256'],'Input manifest changed during replay')
    need(sha(HERE/'DEPENDENCY_PINS.json')==plan['dependency_pins_sha256'],'Dependency pins changed during replay')
    audit=(logs/'Primal80FourierAudit.stdout').read_text()
    need('PRIMAL80_FOURIER_AUDIT_PASS roots=13 edges=6' in audit,'Missing actual audit marker')
    need('PRIMAL80_NEW_SOURCE_CLOSURE_PASS' in audit,'Missing new-only source consumption audit')
    need('sorryAx' not in audit and 'Lean.ofReduceBool' not in audit,'Forbidden axiom')
    rss=[int(x) for p in logs.glob('*.stderr') for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())]
    result=dict(status='PASS_FRESH_DEGREE80_TRUE_FOURIER_ADAPTER',module_count=len(rows),elapsed_seconds=time.monotonic()-started,maximum_recorded_per_process_rss_kib=max(rss),aggregate_peak_not_measured=True,standard_axioms=['propext','Classical.choice','Quot.sound'],source_first_PV=False,mathlib_fourier_pair_proved=True,numerical_upper_bound_or_CMS_consumer=False,commands=results,plan_sha256=sha(out/'PLAN.json'),controller_sha256=controller_sha256)
    pending=out/'RESULT.pending';pending.write_text(json.dumps(result,indent=2)+'\n');os.link(pending,out/'RESULT.json');pending.unlink()
    print(json.dumps({k:v for k,v in result.items() if k!='commands'}))
if __name__=='__main__':main()
