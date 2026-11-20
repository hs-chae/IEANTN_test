#!/usr/bin/env python3
"""Compile one new application module against the exact existing generic pins."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,resource,subprocess,time
S=Path(__file__).resolve().parents[1]
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('module');p.add_argument('--core',action='store_true');p.add_argument('--cpus',default='0,1,2,3');p.add_argument('--memory-gib',type=int,default=48);p.add_argument('--source-root',type=Path);p.add_argument('--audit-root',type=Path);a=p.parse_args()
need(1<=a.memory_gib<=300,'owner-authorized maximum300GiB per run')
available_kib=int(next(line.split()[1]for line in Path('/proc/meminfo').read_text().splitlines()if line.startswith('MemAvailable:')))
available_bytes=available_kib*1024
if a.memory_gib>48:
    need(available_bytes>=1024**4,'high-resource proof run requires genuinely available1TiB RAM')
need(a.memory_gib*1024**3+512*1024**3<=available_bytes,'preserve512GiB host/other-process reserve')
c=json.loads((S/'BUILD_CONTEXT.json').read_text());compiler=Path(c['compiler']);need(sha(compiler)==c['compiler_sha256'],'pinned Lean compiler')
scratch_parent=Path(c['new_application_object_root']).resolve().parent
need(not(a.core and a.source_root is not None),'choose core or generated source root')
if a.source_root is not None:
    need(a.source_root.is_absolute() and a.source_root.resolve().is_relative_to(scratch_parent),'generated source root must be in this experiment-owned scratch tree')
root=a.source_root.resolve() if a.source_root is not None else (S.parents[1] if a.core else S)
if a.audit_root is not None:
    need(a.audit_root.is_absolute() and a.audit_root.resolve().is_relative_to(scratch_parent),'generated audit root must be experiment-owned scratch')
audit_parent=a.audit_root.resolve() if a.audit_root is not None else ((root/'audit') if a.source_root is not None else (S/'audit'))
relative=Path(*a.module.split('.')).with_suffix('.lean');source=root/relative
need(source.is_file()and source.resolve().is_relative_to(root),'exact selected source module')
objects=Path(c['new_application_object_root']);out=objects/relative.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
audit=audit_parent/a.module;attempt=1
while(audit/str(attempt)).exists():attempt+=1
audit=audit/str(attempt);audit.mkdir(parents=True)
source_before=source.read_bytes();source_before_sha=hashlib.sha256(source_before).hexdigest();(audit/'source.lean').write_bytes(source_before)
cpus={int(x)for x in a.cpus.split(',')};need(cpus<=os.sched_getaffinity(0)and 0<len(cpus)<=4,'actual bounded CPU affinity')
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(a.memory_gib*1024**3,a.memory_gib*1024**3));os.sched_setaffinity(0,cpus)
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(objects),*c['generic_libraries']]))
command=['/usr/bin/time','-v','-o',str(audit/'rusage.txt'),str(compiler),'-j1','-R',str(root),str(source),'-o',str(out)]
started=time.monotonic()
with(audit/'stdout').open('w')as stdout,(audit/'stderr').open('w')as stderr:
    result=subprocess.run(command,cwd=root,env=env,stdout=stdout,stderr=stderr,preexec_fn=limits)
source_unchanged=sha(source)==source_before_sha
receipt={'status':('COMPILED' if source_unchanged else 'SOURCE_CHANGED_DURING_COMPILE')if result.returncode==0 else'FAILED_ATTEMPT_PRESERVED','module':a.module,'source':str(source),'source_sha256':source_before_sha,'source_unchanged_during_compile':source_unchanged,'command':command,'returncode':result.returncode,'elapsed_seconds':time.monotonic()-started,'compiler_sha256':sha(compiler),'generic_dependency_context_sha256':sha(S/'BUILD_CONTEXT.json'),'LEAN_PATH':env['LEAN_PATH'],'affinity':sorted(cpus),'memory_limit_bytes':a.memory_gib*1024**3,'host_memavailable_before_bytes':available_bytes,'host_reserve_bytes':512*1024**3,'stdout_sha256':sha(audit/'stdout'),'stderr_sha256':sha(audit/'stderr'),'rusage_sha256':sha(audit/'rusage.txt'),'no_new_verification_workflow_receipt_claimed':True,'timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat()}
if result.returncode==0:receipt['object_sha256']=sha(out)
(audit/'RUN.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'status':receipt['status'],'returncode':result.returncode,'elapsed_seconds':receipt['elapsed_seconds'],'audit':str(audit)},sort_keys=True))
raise SystemExit(result.returncode if source_unchanged else 2)
