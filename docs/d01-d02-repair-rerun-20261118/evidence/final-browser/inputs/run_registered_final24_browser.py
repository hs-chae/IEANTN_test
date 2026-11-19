"""One zero-model report browser check in the existing shared resource registry."""
from pathlib import Path
import argparse,fcntl,hashlib,importlib.util,json,os,signal,subprocess,sys,time
sys.dont_write_bytecode=True
S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-deep-tertiary-exposure-a-20261117')
ADMIN_ROOT=Path('/data/ivy-d01-d02-final-browser-20261119')
CHECKER=S/'scripts/check_final_publication_browser.py'
QUEUE=S/'scripts/run_review_queue.py'
QUEUE_SHA='b1d1f6b61fd3aaaac9a2f24e6980bb286f8e5282699da15762846003483a4f68'
STOP=False

def need(c,m):
    if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p):return {'path':str(p),'sha256':sha(p)}
def module(n,p):
    spec=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(spec);sys.modules[n]=m;spec.loader.exec_module(m);return m

def request_stop(number,frame):
    global STOP
    STOP=True

def release(q,reservation):
    need(not q.resources.unit_alive(reservation),'browser owned unit not drained; reservation retained')
    raw=reservation.get('cgroup')
    if raw:
        group=Path('/sys/fs/cgroup')/raw.lstrip('/')
        need(all(not p.read_text().strip() for p in group.rglob('cgroup.procs')),'browser descendant cgroup not drained; reservation retained')
    with (q.resources.GLOBAL_ADMIN/'allocations.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);p=q.resources.GLOBAL_ADMIN/'allocations.json';d=q.load(p)
        own=[r for r in d['allocations'] if r.get('participant')=='A' and r.get('unit')==reservation['unit']]
        need(len(own)==1,'browser reservation census differs')
        d['allocations']=[r for r in d['allocations'] if not(r.get('participant')=='A' and r.get('unit')==reservation['unit'])]
        q.resources.atomic(p,d)

def main():
    p=argparse.ArgumentParser(description=__doc__,allow_abbrev=False);p.add_argument('--config',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--root-authorization',type=Path)
    modes=p.add_mutually_exclusive_group(required=True);modes.add_argument('--check',action='store_true');modes.add_argument('--run',action='store_true');a=p.parse_args()
    a.config,a.out=a.config.resolve(),a.out.resolve()
    need(ADMIN_ROOT.is_dir() and not ADMIN_ROOT.is_symlink() and ADMIN_ROOT.resolve()==ADMIN_ROOT and ADMIN_ROOT.stat().st_uid==os.getuid(),'exact owned browser resource root required')
    need(a.out.is_relative_to(ADMIN_ROOT/'evidence') and not a.out.exists(),'fresh owned browser output required')
    need(sha(QUEUE)==QUEUE_SHA,'pinned shared resource helper changed')
    checker=module('final_publication_checker_metadata',CHECKER)
    config=checker.configuration(a.config)
    identities=[pin(Path(__file__).resolve()),pin(CHECKER),pin(QUEUE),pin(S/'scripts/run_block_v2.py')]
    if a.run:
        need(a.root_authorization is not None,'ROOT exact final-report browser authority required before any scope')
        auth=checker.load(a.root_authorization.resolve())
        need(auth.get('schema')=='FINAL_PUBLICATION_BROWSER_ROOT_V1' and auth.get('status')=='ROOT_AUTHORIZED_PINNED_FINAL_REPORT_BROWSER_CHECK' and auth.get('reviewed_by')=='/root' and type(auth.get('model_calls')) is int and auth['model_calls']==0,'ROOT final browser authorization status differs')
        need(auth.get('source_pins')==identities and auth.get('configuration')==pin(a.config) and auth.get('approved_out')==str(a.out) and auth.get('browser')==config['browser'],'ROOT browser source/artifact/resource authority differs')
    if a.check:
        print(json.dumps({'status':'PASS_REGISTERED_BROWSER_METADATA_ONLY_NO_SCOPE','configuration':pin(a.config),'source_pins':identities,'browser':config['browser'],'model_calls':0}));return
    signal.signal(signal.SIGTERM,request_stop);signal.signal(signal.SIGINT,request_stop)
    q=module('registered_publication_existing_resources',QUEUE)
    need(q.resources.GLOBAL_ADMIN.resolve()==S.parent/'EXPOSURE_LONGCHAIN_20261117_V1_RESOURCES','original shared registry preserved')
    q.S=ADMIN_ROOT  # The unchanged allocator checks the actual browser-output filesystem.
    lease,reservation=q.reserve_one('ADMIN-FINAL-PUBLICATION-BROWSER-'+a.out.name)
    process=None;stdout=stderr=None;samples=[];error=None;code=None;started=time.monotonic();drained=False;released=False
    try:
        a.out.mkdir();(a.out/'tmp').mkdir()
        need(not STOP,'browser check interrupted before scope')
        command=['systemd-run','--user','--wait','--collect','--pipe','--unit='+reservation['unit'],'--property=MemoryMax=64G','--property=MemorySwapMax=0','--property=TasksMax=512','--property=LimitNOFILE=65536','--property=KillMode=control-group','--property=TimeoutStopSec=15','--property=RuntimeMaxSec=600','--setenv=PATH='+os.environ['PATH'],'--setenv=TMPDIR='+str(a.out/'tmp'),'/usr/bin/time','-v','-o',str(a.out/'PROCESS_RUSAGE.txt'),'/usr/bin/taskset','--cpu-list',','.join(map(str,reservation['CPU_affinity'])),sys.executable,'-I','-B',str(CHECKER),'--config',str(a.config),'--execute','--out',str(a.out/'render'),'--cpus',','.join(map(str,reservation['CPU_affinity'])),'--unit',reservation['unit']]
        checker.atomic(a.out/'INVOCATION.json',{'command':command,'source_pins':identities,'configuration':pin(a.config),'ROOT':pin(a.root_authorization.resolve()),'reservation':reservation,'model_calls':0})
        stdout=(a.out/'scope.stdout').open('x');stderr=(a.out/'scope.stderr').open('x');process=subprocess.Popen(command,stdout=stdout,stderr=stderr)
        for _ in range(200):
            need(not STOP,'browser check interrupted during startup')
            if q.resources.unit_alive(reservation):break
            need(process.poll() is None,'browser unit exited before resource publication');time.sleep(.05)
        group=q.resources.ctl('show',reservation['unit'],'--property=ControlGroup','--value').stdout.strip();need(group.startswith('/'),'browser actual cgroup unavailable');reservation['cgroup']=group
        registry=q.resources.GLOBAL_ADMIN/'allocations.json';d=q.load(registry);own=[r for r in d['allocations'] if r.get('participant')=='A' and r.get('unit')==reservation['unit']];need(len(own)==1,'browser reservation disappeared');own[0]['cgroup']=group;q.resources.atomic(registry,d);lease.close();lease=None
        while process.poll() is None:
            samples.append(q.resources.cgroup_sample(reservation['unit']))
            usage=q.resources.owned_file_usage(a.out)
            if STOP or time.monotonic()-started>=610 or usage['apparent_bytes']>25*1024**3:
                raise RuntimeError('browser interrupted/wall/scratch allowance exceeded')
            time.sleep(.5)
        code=process.wait();need(code==0,'browser render failed; preserve exact attempt and stop')
        result=a.out/'render/RECEIPT.json';d=checker.load(result);need(d.get('status')=='PASS_PINNED_STANDALONE_DESKTOP_MOBILE_REPORT_RENDER' and d.get('model_calls')==0,'actual browser receipt missing/differs')
        need(identities==[pin(Path(__file__).resolve()),pin(CHECKER),pin(QUEUE),pin(S/'scripts/run_block_v2.py')] and checker.configuration(a.config)==config,'browser source/configuration changed')
    except BaseException as e:error={'type':type(e).__name__,'message':str(e)}
    finally:
        try:
            if process is not None:q.stop_and_drain_owned(reservation,process)
            drained=not q.resources.unit_alive(reservation)
        except BaseException as cleanup:
            error={'type':type(cleanup).__name__,'message':'owned browser cleanup: '+str(cleanup),'prior_error':error}
        finally:
            if lease is not None:lease.close()
            if stdout is not None:stdout.close()
            if stderr is not None:stderr.close()
        if drained:
            try:release(q,reservation);released=True
            except BaseException as cleanup:error={'type':type(cleanup).__name__,'message':'owned browser reservation release: '+str(cleanup),'prior_error':error}
    need(a.out.exists(),'browser failed before evidence directory creation')
    checker.atomic(a.out/'RESOURCE_SAMPLES.json',samples)
    receipt={'schema':'REGISTERED_FINAL_PUBLICATION_BROWSER_RESOURCE_RECEIPT_V1','status':'PASS_REGISTERED_FINAL_REPORT_BROWSER_SCOPE_DRAINED' if error is None and drained else 'FAILED_BROWSER_ATTEMPT_PRESERVED_NO_RETRY','source_pins':identities,'configuration':pin(a.config),'ROOT':pin(a.root_authorization.resolve()),'reservation':reservation,'returncode':code,'error':error,'execution_drained':drained,'reservation_released_foreign_rows_preserved':released,'elapsed_seconds':time.monotonic()-started,'sampled_charged_memory_peak_lower_bound_bytes':max((r.get('memory.current') or 0 for r in samples),default=0),'exact_kernel_memory_peak_bytes':max((r['memory.peak'] for r in samples if r.get('memory.peak') is not None),default=None),'memory_events_last_observed':next((r.get('memory.events') for r in reversed(samples) if r.get('memory.events') is not None),None),'retained_output_usage':q.resources.owned_file_usage(a.out),'exact_disk_peak_inferred':False,'model_calls':0,'downloads_requested':0,'mathematical_truth_or_PV_assessed':False,'actual_output_resource_root':str(ADMIN_ROOT),'shared_registry':str(q.resources.GLOBAL_ADMIN)}
    if error is None:receipt['browser_receipt']=pin(a.out/'render/RECEIPT.json')
    checker.atomic(a.out/'REGISTERED_RESOURCE_RECEIPT.json',receipt)
    need(error is None and drained,'registered browser attempt failed; retain evidence without retry')
    print(json.dumps({'status':receipt['status'],'receipt':pin(a.out/'REGISTERED_RESOURCE_RECEIPT.json')}))

if __name__=='__main__':main()
