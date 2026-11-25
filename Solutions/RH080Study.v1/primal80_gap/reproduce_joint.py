#!/usr/bin/env python3
"""Fresh complete new degree80 certificate/Fourier/CMS consumer source closure.

The only cached libraries are pinned Mathlib dependencies. All numerical cells,
generic LeanCert sources, actual Fourier proofs and v2 adapters are rebuilt.
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
    parser.add_argument('--workers',type=int,choices=range(1,9),default=8)
    parser.add_argument('--worker-memory-gib',type=int,choices=[32,64],default=32)
    parser.add_argument('--reuse-cold-leaves',type=Path)
    parser.add_argument('--accepted-new-cell-bank',type=Path)
    args=parser.parse_args();out=args.out.resolve()
    need(not out.exists(),'Fresh output directory required')
    need(args.accepted_new_cell_bank is None or args.reuse_cold_leaves is not None,'New cell bank is only permitted with an explicit compound cold-leaf repair')
    context=json.loads(args.context.read_text());pins=json.loads((STUDY/'primal80_fourier/DEPENDENCY_PINS.json').read_text())
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
    need(aggregate_allowance<=256*2**30,'Aggregate compiler address-space allowance exceeds authorized256GiB')
    admission_memory=available_memory();admission_disk=shutil.disk_usage(out.parent).free
    need(admission_memory>=256*2**30+aggregate_allowance,'Host reserve plus worker capacity unavailable')
    need(admission_disk>=2**40,'Independent free disk below1TiB')
    mappings={
      'Primal80WitnessSolution':REPO/'Solutions/GaussianFourierWitness.v2/Solution.lean',
      'Primal80AsymptoticSolution':REPO/'Solutions/RHAsymptoticGaussian.v2/Solution.lean'}
    roots=[REPO,HERE,STUDY/'primal80_fourier',STUDY/'functional/primal40',
      REPO/'Solutions/RHOnePrimeEvolution.v1/gaussian_fourier',
      REPO/'Solutions/RHOnePrimeEvolution.v1/gaussian_kernel',
      REPO/'Solutions/RHOnePrimeEvolution.v1/gaussian_gap',args.lean_cert_source]
    forbidden={'GaussianPhysical','GaussianWings','GaussianEligibility','GaussianNumericalWitness',
      'GaussianCanonicalConsumers','GaussianAsymptoticConsumers','GaussianActualTransform',
      'GaussianActualFourier','GaussianFiniteNorm','GaussianFiniteWing','GaussianFullRays'}
    seen=set();order=[];dependencies={}
    def generic(module):return module.startswith(('Mathlib','Lean.','Std.','Init.')) or module in ('Lean','Std','Init')
    def visit(module):
        if generic(module) or module in seen:return
        need(module not in forbidden and not module.startswith('GaussianCells'),'Old actual numerical/Fourier witness leaf imported '+module)
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
    visit('Primal80CanonicalAudit')
    out.mkdir(parents=True);source_root=out/'source';objects=out/'objects';logs=out/'logs'
    for path in (source_root,objects,logs):path.mkdir()
    rows=[]
    for module,source in order:
        target=source_root/(module.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(source.read_bytes())
        rows.append(dict(module=module,original=str(source),source_sha256=sha(source),imports=dependencies[module]))
    plan=dict(status='FROZEN_COMPLETE_NEW_SOURCE_CLOSURE',compiler=context['compiler'],compiler_sha256=sha(Path(context['compiler'])),generic_lean_path=context['generic_lean_path'],modules=rows,controller_sha256=controller_hash,context_sha256=context_hash,workers=args.workers,per_process_AS_bytes=args.worker_memory_gib*2**30,aggregate_AS_allowance_bytes=aggregate_allowance,host_reserve_bytes=256*2**30,admission_MemAvailable_bytes=admission_memory,admission_disk_free_bytes=admission_disk,application_or_LeanCert_object_cache_used=args.reuse_cold_leaves is not None,reuse_requested=str(args.reuse_cold_leaves) if args.reuse_cold_leaves else None,accepted_new_cell_bank_sha256=sha(args.accepted_new_cell_bank) if args.accepted_new_cell_bank else None,policy='Coordinatorproofreproduction/repairoutsidefrozenexperimentaltrials; authorized8workersx32GiBaggregate256GiB. Historicaltrial4CPU64GiBbudgetsunchanged.')
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
    if args.reuse_cold_leaves is not None:
        cold=args.reuse_cold_leaves.resolve();cold_plan=json.loads((cold/'PLAN.json').read_text())
        need(cold_plan['compiler_sha256']==plan['compiler_sha256'],'Cold compiler identity differs')
        need(cold_plan['generic_lean_path']==context['generic_lean_path'],'Cold generic library identity differs')
        cold_rows={row['module']:row for row in cold_plan['modules']}
        for row in rows:
            module=row['module'];previous=cold_rows.get(module)
            if module=='Primal80CanonicalAudit':continue
            if previous is None or previous['source_sha256']!=row['source_sha256']:continue
            if not set(row['imports'])<=done:continue
            old_source=cold/'source'/(module.replace('.','/')+'.lean');old_object=cold/'objects'/(module.replace('.','/')+'.olean');stem=module.replace('.','_')
            old_stdout=cold/'logs'/(stem+'.stdout');old_stderr=cold/'logs'/(stem+'.stderr')
            if not all(p.is_file() for p in [old_source,old_object,old_stdout,old_stderr]):continue
            stderr=old_stderr.read_text()
            if 'Exit status: 0' not in stderr or 'terminated by signal' in stderr:continue
            need(sha(old_source)==row['source_sha256'],'Cold captured source differs')
            object_hash=sha(old_object);target=objects/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(old_object.read_bytes())
            need(sha(target)==object_hash==sha(old_object),'Cold object changed during association')
            record=dict(module=module,action='reuse_exact_unchanged_new_cold_leaf',source_sha256=row['source_sha256'],object_sha256=object_hash,source_cold_directory=str(cold),cold_plan_sha256=sha(cold/'PLAN.json'),cold_controller_sha256=cold_plan['controller_sha256'],compiler_sha256=cold_plan['compiler_sha256'],cold_stdout_sha256=sha(old_stdout),cold_stderr_sha256=sha(old_stderr),cold_success_evidence='CapturedGNUtimeExitstatus0;exactcapturedsource/current-source/objectassociation;finalStd3auditstillrequired.')
            reused.append(record);done.add(module);del remaining[module]
        if args.accepted_new_cell_bank is not None:
            bank=json.loads(args.accepted_new_cell_bank.read_text())
            need(bank['status']=='ALL25_NEW_DEGREE80_CELL_MODULES_1193_CELLS_COMPILED_SOURCE_OBJECT_IDENTITIES_MATCH','Unaccepted new-cell bank status')
            bank_rows={item['module']:item for item in bank['rows']}
            need(len(bank_rows)==len(bank['rows'])==25,'New-cell bank identity collapse or population differs')
            for row in rows:
                module=row['module']
                if not module.startswith('G40Cells') or module in done:continue
                need(set(row['imports'])<=done,'New-cell prerequisites not freshly associated')
                item=bank_rows.get(module);need(item is not None,'Missing explicit new-cell row '+module)
                source=Path(item['source']);object_file=Path(item['object']);batch=Path(item['batch_receipt'])
                need(item['source_sha256']==row['source_sha256']==sha(source),'New-cell captured/current source differs')
                need(item['object_sha256']==sha(object_file),'New-cell object differs')
                need(item['batch_receipt_sha256']==sha(batch),'New-cell batch receipt differs')
                receipt=json.loads(batch.read_text());need(receipt['status']=='PASS_EXPLICIT_SELECTED_CELL_COMPILATION','New-cell batch not accepted')
                need(receipt['compiler_sha256']==plan['compiler_sha256'],'New-cell compiler identity differs')
                run=next((entry for entry in receipt['actual_runs'] if entry['module']==module),None)
                need(run is not None and run['returncode']==0 and run['accepted'] is True,'New-cell actual compiler run absent/rejected')
                need(run['source_sha256']==row['source_sha256'] and run['object_sha256']==item['object_sha256'],'New-cell actual run identities differ')
                need(run['command']==item['command'],'New-cell actual command differs')
                logdir=Path(item['logs']);stdout=logdir/(module+'.stdout');stderr=logdir/(module+'.stderr');metrics=logdir/(module+'.time')
                need(sha(stdout)==run['stdout_sha256'] and sha(stderr)==run['stderr_sha256'] and sha(metrics)==run['metrics_sha256'],'New-cell actual logs differ')
                need('Exit status: 0' in metrics.read_text(),'New-cell GNUtime success absent')
                target=objects/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(object_file.read_bytes())
                need(sha(target)==item['object_sha256'],'Copied new-cell object differs')
                reused.append(dict(module=module,action='reuse_explicit_accepted_new_cell_bank',source_sha256=row['source_sha256'],object_sha256=item['object_sha256'],batch_receipt_sha256=sha(batch),batch_controller_sha256=receipt['controller_sha256'],compiler_sha256=receipt['compiler_sha256'],actual_command=run['command'],actual_stdout_sha256=run['stdout_sha256'],actual_stderr_sha256=run['stderr_sha256'],actual_metrics_sha256=run['metrics_sha256'],bank_manifest_sha256=sha(args.accepted_new_cell_bank)))
                done.add(module);del remaining[module]
        # A repair run must not silently repeat expensive incomplete cells.
        missing=[row['module'] for row in rows if row['module'].startswith('G40Cells') and row['module'] not in done]
        need(not missing,'Not every new cell source has completed in cold bank: '+','.join(missing))
        (out/'REUSED_COLD_LEAVES.json').write_text(json.dumps(reused,indent=2)+'\n')
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
    audit=(logs/'Primal80CanonicalAudit.stdout').read_text()
    need('PRIMAL80_CANONICAL_AUDIT_PASS roots=15 edges=12' in audit,'Missing final actual type/value/input audit')
    need('PRIMAL80_COMPLETE_NEW_SOURCE_CLOSURE_PASS' in audit,'Missing new-only source closure audit')
    need('sorryAx' not in audit and 'Lean.ofReduceBool' not in audit,'Forbidden printed axiom')
    rss=[int(x) for p in logs.glob('*.stderr') for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())]
    status='PASS_COMPOUND_NEW_COLD_LEAVES_AND_REPAIRED_DOWNSTREAM' if reused else 'PASS_COMPLETE_NEW_DEGREE80_CERTIFICATE_FOURIER_CMS_V2_CONSUMERS'
    result=dict(status=status,full_clean_cold_reproduction=not reused,exact_coefficient='2746403660/3293251743',strict_readable_bound='833948898/1000000000',modules=len(rows),newly_compiled_modules=len(results),reused_same_source_new_cold_modules=len(reused),seconds=time.monotonic()-start,workers=args.workers,per_process_AS_bytes=args.worker_memory_gib*2**30,maximum_recorded_per_process_GNU_RSS_kib=max(rss),sampled_aggregate_RSS_max_bytes=max(item['RSS_bytes'] for item in samples),sampled_aggregate_RSS_interval_seconds=0.5,minimum_sampled_host_MemAvailable_bytes=min(item['MemAvailable_bytes'] for item in samples),aggregate_exact_peak_not_measured=True,final_directory_bytes=sum(p.stat().st_size for p in out.rglob('*') if p.is_file()),peak_disk_not_measured=True,source_first_PV=False,official_Comparator=False,assumptions='OnlyunchangedgeneralCMSFunctionalInput.v1gap/populationsourcepredicatesplusordinaryRHforANT; actualFourierandnumericwitnessclosed.',standard_axioms=['propext','Classical.choice','Quot.sound'],plan_sha256=sha(out/'PLAN.json'),controller_sha256=controller_hash,commands=results,reused_cold_leaves=reused)
    publish(out/'RESULT.json',result)
    print(json.dumps({k:v for k,v in result.items() if k not in ['commands','reused_cold_leaves']}))

if __name__=='__main__':main()
