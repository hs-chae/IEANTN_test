#!/usr/bin/env python3
"""Fresh complete new degree56 certificate/Fourier/CMS consumer source closure.

The only cached libraries are pinned Mathlib dependencies. All numerical cells,
generic LeanCert sources, actual Fourier proofs and v3 adapters are rebuilt.
"""
import argparse, concurrent.futures, hashlib, json, os, re, shutil, subprocess, threading, time
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
STUDY=HERE.parent

def need(ok,message):
    if not ok:raise RuntimeError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def available_memory():
    return int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')))*1024
def process_tree_rss(pid):
    todo=[pid];seen=set();rss=0
    while todo:
        current=todo.pop()
        if current in seen:continue
        seen.add(current)
        try:
            status=Path('/proc')/str(current)/'status'
            rss+=sum(int(line.split()[1])*1024 for line in status.read_text().splitlines() if line.startswith('VmRSS:'))
            # A child launched by ThreadPoolExecutor belongs to its spawning
            # task's children file, not necessarily the process leader's file.
            for task in (Path('/proc')/str(current)/'task').iterdir():
                try:todo += [int(value) for value in (task/'children').read_text().split()]
                except (FileNotFoundError,ProcessLookupError):pass
        except (FileNotFoundError,ProcessLookupError):pass
    return rss,len(seen)
def publish(path,data):
    need(not path.exists(),'Fresh acceptance path required')
    temporary=path.with_suffix('.pending');temporary.write_text(json.dumps(data,indent=2)+'\n')
    os.link(temporary,path);temporary.unlink()

def main():
    parser=argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--context',type=Path,default=Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json'))
    parser.add_argument('--lean-cert-source',type=Path,default=Path('/data/ivy-rh-080-20261125/baseline/gaussian53-v1/run/compile/source'))
    parser.add_argument('--workers',type=int,choices=range(1,5),default=4)
    parser.add_argument('--worker-memory-gib',type=int,choices=[32,64],default=32)
    args=parser.parse_args();out=args.out.resolve()
    need(not out.exists(),'Fresh output directory required')
    context=json.loads(args.context.read_text());pins=json.loads((STUDY/'primal56_fourier/DEPENDENCY_PINS.json').read_text())
    controller_hash=sha(Path(__file__));context_hash=sha(args.context)
    need(context['compiler_sha256']==pins['compiler_sha256']==sha(Path(context['compiler'])),'Compiler identity differs')
    need(context['compiler_version']==pins['compiler_version']==subprocess.check_output([context['compiler'],'--version'],text=True).strip(),'Compiler version differs')
    need(context['generic_dependencies']==pins['generic_dependencies'],'Generic dependency pins differ')
    paths=context['generic_lean_path'].split(':')
    need(len(paths)==len(pins['generic_dependencies']),'Generic path population differs')
    for path,dep in zip(paths,pins['generic_dependencies']):
        pkg=Path(path).parents[3]
        need(pkg.name==dep['name'],'Generic path order differs')
        need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=pkg,text=True).strip()==dep['revision'],'Generic source revision differs')
        need(not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=pkg,text=True),'Generic tracked source dirty')
    aggregate_allowance=args.workers*args.worker_memory_gib*2**30
    need(aggregate_allowance<=256*2**30 and args.workers<=4,'Compiler policy exceeds4workers/256GiB')
    admission_memory=available_memory();admission_disk=shutil.disk_usage(out.parent).free
    need(admission_memory>=256*2**30+aggregate_allowance,'Host reserve plus worker capacity unavailable')
    need(admission_disk>=2**40,'Independent free disk below1TiB')
    inputs_path=STUDY/'primal56_fourier/INPUTS.json';input_hash=sha(inputs_path)
    inputs=json.loads(inputs_path.read_text())
    for item in inputs['source_inputs']:
        need(sha(REPO/item['path'])==item['sha256'],'Frozen original/candidate/physical input differs')
    for filename,key in [('Primal56CoefficientTransform.lean','generated_sha256'),('Primal56OriginalInput.lean','original_input_module_sha256')]:
        need(sha(STUDY/'primal56_fourier'/filename)==inputs[key],'Exact original/transform module differs')
    need(sha(STUDY/'functional/primal28/G28Functions.lean')=='a980dc111cdf6d49e59b2dbb5d55b5f595e42ee348e5e0115e619082f1025a34','Frozen actual physical functions differ')
    mappings={
      'Primal56WitnessSolution':REPO/'Solutions/GaussianFourierWitness.v3/Solution.lean',
      'Primal56AsymptoticSolution':REPO/'Solutions/RHAsymptoticGaussian.v3/Solution.lean'}
    roots=[REPO,HERE,STUDY/'primal56_fourier',STUDY/'functional/primal28',STUDY/'functional/primal40',
      REPO/'Solutions/RHOnePrimeEvolution.v1/gaussian_fourier',
      REPO/'Solutions/RHOnePrimeEvolution.v1/gaussian_kernel',
      REPO/'Solutions/RHOnePrimeEvolution.v1/gaussian_gap',args.lean_cert_source]
    forbidden={'Primal80ActualFourier','Primal80CoefficientTransform','Primal80Eligibility','Primal80NumericalWitness','Primal80ActualConsumers','Primal80CanonicalConsumers','G40Physical','G40Wings','G40Functions','G40Sources','G40FiniteNorm','G40FiniteWing','G40FullRays','GaussianPhysical','GaussianWings','GaussianEligibility','GaussianNumericalWitness',
      'GaussianCanonicalConsumers','GaussianAsymptoticConsumers','GaussianActualTransform',
      'GaussianActualFourier','GaussianFiniteNorm','GaussianFiniteWing','GaussianFullRays'}
    seen=set();order=[];dependencies={}
    def generic(module):return module.startswith(('Mathlib','Lean.','Std.','Init.')) or module in ('Lean','Std','Init')
    def visit(module):
        if generic(module) or module in seen:return
        need(module not in forbidden and not module.startswith(('GaussianCells','G40Cells')),'Old actual numerical/Fourier witness leaf imported '+module)
        seen.add(module)
        candidates=[mappings.get(module)]+[p/(module.replace('.','/')+'.lean') for p in roots]
        source=next((p for p in candidates if p and p.is_file()),None)
        need(source is not None,'Missing local source '+module)
        imports=[]
        for line in source.read_text().splitlines():
            if line.startswith('import '):imports+=line[7:].split('--',1)[0].split()
        dependencies[module]=[m for m in imports if not generic(m)]
        for dependency in imports:visit(dependency)
        order.append((module,source))
    visit('Primal56CanonicalAudit')
    out.mkdir(parents=True);source_root=out/'source';objects=out/'objects';logs=out/'logs'
    for path in (source_root,objects,logs):path.mkdir()
    rows=[]
    for module,source in order:
        target=source_root/(module.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(source.read_bytes())
        rows.append(dict(module=module,original=str(source),source_sha256=sha(source),imports=dependencies[module]))
    plan=dict(status='FROZEN_COMPLETE_NEW_SOURCE_CLOSURE',compiler=context['compiler'],compiler_sha256=sha(Path(context['compiler'])),generic_lean_path=context['generic_lean_path'],modules=rows,controller_sha256=controller_hash,context_sha256=context_hash,workers=args.workers,per_process_AS_bytes=args.worker_memory_gib*2**30,aggregate_AS_allowance_bytes=aggregate_allowance,host_reserve_bytes=256*2**30,admission_MemAvailable_bytes=admission_memory,admission_disk_free_bytes=admission_disk,application_or_LeanCert_object_cache_used=False,policy='Additiveprospectiveproofreproductionoutsidefrozenexperimentaltrials;4workers32or64GiBaggregate<=256GiB;historicaltrialbudgetsandoutcomesunchanged.')
    (out/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n');(out/'reproduce_joint.executed.py').write_bytes(Path(__file__).read_bytes())
    env=os.environ.copy();env['LEAN_PATH']=str(objects)+':'+context['generic_lean_path']
    def compile_one(row):
        module=row['module'];source=source_root/(module.replace('.','/')+'.lean');target=objects/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
        stem=module.replace('.','_');stdout=logs/(stem+'.stdout');stderr=logs/(stem+'.stderr')
        command=['/usr/bin/prlimit','--as='+str(args.worker_memory_gib*2**30),'--','/usr/bin/time','-v',context['compiler'],'-j2','--root='+str(source_root),'-o',str(target),str(source)]
        start=time.monotonic()
        with stdout.open('wb') as o,stderr.open('wb') as e:run=subprocess.run(command,env=env,stdout=o,stderr=e)
        return dict(module=module,returncode=run.returncode,seconds=time.monotonic()-start,command=command,source_sha256=sha(source),object_sha256=sha(target) if target.exists() else None,stdout_sha256=sha(stdout),stderr_sha256=sha(stderr))
    remaining={row['module']:row for row in rows};done=set();running={};results=[];reused=[];start=time.monotonic();failed=None
    stop_sampling=threading.Event();samples=[]
    def sampler():
        while not stop_sampling.is_set():
            rss,processes=process_tree_rss(os.getpid())
            samples.append(dict(seconds=time.monotonic()-start,RSS_bytes=rss,processes=processes,MemAvailable_bytes=available_memory()))
            stop_sampling.wait(0.5)
    sampling_thread=threading.Thread(target=sampler,daemon=True);sampling_thread.start()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        while remaining or running:
            if failed is None:
                ready=[row for row in remaining.values() if set(row['imports'])<=done]
                for row in ready:
                    if len(running)>=args.workers:break
                    need(available_memory()>=256*2**30,'Available-host reserve fell below256GiB')
                    future=pool.submit(compile_one,row);running[future]=row['module'];del remaining[row['module']]
            need(running or failed is not None,'Dependency scheduling stalled')
            if not running:break
            finished,_=concurrent.futures.wait(running,timeout=30,return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                module=running.pop(future);record=future.result();results.append(record)
                if record['returncode']:
                    failed=record;(out/'FAILED.json').write_text(json.dumps(record,indent=2)+'\n')
                    print('FAILED',module,flush=True)
                else:
                    done.add(module);print(module,'PASS',flush=True)
                (out/'PROGRESS.json').write_text(json.dumps(dict(compiled=len(results),required=len(rows),running=list(running.values()),last=module,failed=failed is not None))+'\n')
    stop_sampling.set();sampling_thread.join()
    (out/'SAMPLED_RESOURCES.json').write_text(json.dumps(dict(interval_seconds=0.5,scope='Thiscontrolleranditsdescendantcompilerprocessesonly;sampledRSSisnotexactpeak.',samples=samples),indent=2)+'\n')
    if failed is not None:raise RuntimeError('Compiler rejected '+failed['module'])
    need(len(done)==len(rows),'Not every active local dependency compiled')
    for row in rows:need(sha(Path(row['original']))==row['source_sha256'],'Source changed during replay '+row['module'])
    need(sha(Path(__file__))==controller_hash,'Controller changed during replay')
    need(sha(args.context)==context_hash,'Context changed during replay')
    need(sha(inputs_path)==input_hash,'Original/physical association input changed during replay')
    audit=(logs/'Primal56CanonicalAudit.stdout').read_text()
    need('PRIMAL56_CANONICAL_AUDIT_PASS roots=17 edges=12' in audit,'Missing final actual type/value/input audit')
    need('PRIMAL56_COMPLETE_NEW_SOURCE_CLOSURE_PASS' in audit,'Missing new-only source closure audit')
    need('sorryAx' not in audit and 'Lean.ofReduceBool' not in audit,'Forbidden printed axiom')
    rss=[int(x) for p in logs.glob('*.stderr') for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())]
    status='PASS_COMPLETE_NEW_DEGREE56_CERTIFICATE_TRUE_FOURIER_ORIGINAL_INPUT_CMS_V3_CONSUMERS'
    result=dict(status=status,full_clean_cold_reproduction=not reused,exact_coefficient='82325773717/98718416336',strict_readable_bound='833945448/1000000000',modules=len(rows),newly_compiled_modules=len(results),reused_same_source_new_cold_modules=len(reused),seconds=time.monotonic()-start,workers=args.workers,per_process_AS_bytes=args.worker_memory_gib*2**30,maximum_recorded_per_process_GNU_RSS_kib=max(rss),sampled_aggregate_RSS_max_bytes=max(item['RSS_bytes'] for item in samples),sampled_aggregate_RSS_interval_seconds=0.5,minimum_sampled_host_MemAvailable_bytes=min(item['MemAvailable_bytes'] for item in samples),aggregate_exact_peak_not_measured=True,final_directory_bytes=sum(p.stat().st_size for p in out.rglob('*') if p.is_file()),peak_disk_not_measured=True,source_first_PV=False,official_Comparator=False,assumptions='OnlyunchangedgeneralCMSFunctionalInput.v1gap/populationsourcepredicatesplusordinaryRHforANT; actualFourierandnumericwitnessclosed.',standard_axioms=['propext','Classical.choice','Quot.sound'],plan_sha256=sha(out/'PLAN.json'),controller_sha256=controller_hash,commands=results,reused_cold_leaves=reused)
    publish(out/'RESULT.json',result)
    print(json.dumps({k:v for k,v in result.items() if k not in ['commands','reused_cold_leaves']}))

if __name__=='__main__':main()
