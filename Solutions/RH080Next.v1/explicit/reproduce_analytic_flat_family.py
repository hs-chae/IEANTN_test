#!/usr/bin/env python3
"""Fresh source-cold reproduction of the general flat-family analytic RH population result.
This is kernel-only analytic verification, not source-first program verification.
Only the eight pinned generic libraries may enter through compiled caches.
"""
from __future__ import annotations
import argparse,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'}
COMPILER_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
PINS={'mathlib':'71a80585ee495fc24472fd0eaffc89d94e4fd8d6','plausible':'d9598f07b1bc701f1e3aae163d2681c1fd978793','LeanSearchClient':'ba67e212be1197b84c1f1f6299488a10a3002713','importGraph':'1681d78dd6e65e38b143f9740d829c826673807c','proofwidgets':'a8acbfd87375ff4abe14ce09db5b7664d383bc7f','aesop':'18889deb9e83ea7420ef51c160d6f88552e744e3','Qq':'507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3','batteries':'4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb'}
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic(p,value):
    need(not p.exists(),'receipt already exists');tmp=p.with_name('.'+p.name+'.tmp')
    with tmp.open('x')as f:json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(tmp,p)
    finally:tmp.unlink()
def imports(p):return[n for l in p.read_text().splitlines()if l.startswith('import ')for n in l[7:].split('--',1)[0].split()]
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--memory-gib',type=int,default=32);a=ap.parse_args()
    need(not a.run.exists(),'fresh experiment-owned run directory required');need(1<=a.memory_gib<=300,'invalid memory allowance')
    c=json.loads(a.context.read_text());need(sha(Path(c['compiler']))==COMPILER_SHA==c['compiler_sha256'],'pinned Lean compiler differs')
    need({d['name']:d['revision']for d in c['generic_dependencies']}==PINS,'generic dependency pins differ')
    generic=c['generic_lean_path'].split(':');need(len(generic)==8,'exactly eight generic library roots required')
    for entry in generic:
        path=Path(entry).resolve();need(path.is_dir(),'generic object root absent')
        repo=path.parents[3];got=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip();need(PINS.get(repo.name)==got,'generic library checkout differs: '+str(repo))
    mem={l.split(':')[0]:int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()}
    need(mem['MemAvailable']>=(a.memory_gib+256)*2**30,'insufficient available RAM after256GiB host reserve')
    a.run.parent.mkdir(parents=True,exist_ok=True);disk=shutil.disk_usage(a.run.parent);need(disk.free>4*2**30,'insufficient free scratch space')
    project=Path(__file__).resolve().parent.parent;repo=project.parents[1]
    bases=[project/'explicit',project/'primal',project/'dual',project/'pv/lean',repo/'Solutions/CH2.v6',repo]
    seen=set();active=set();rows=[]
    def visit(n):
        if n in seen or n.split('.')[0]in GENERIC:return
        need(n not in active,'application import cycle');active.add(n)
        paths=[p for b in bases if(p:=b/(n.replace('.','/')+'.lean')).is_file()];need(len(paths)==1,'application source must resolve uniquely: '+n);p=paths[0]
        for child in imports(p):visit(child)
        active.remove(n);seen.add(n);rows.append(dict(module=n,origin=str(p),source_sha256=sha(p),imports=imports(p)))
    visit('AnalyticFlatFamilyAudit');a.run.mkdir()
    for n in ['source','objects','logs']:(a.run/n).mkdir()
    for r in rows:
        p=a.run/'source'/(r['module'].replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(Path(r['origin']).read_bytes());r['snapshot']=str(p)
    atomic(a.run/'PLAN.json',dict(roots=['AnalyticFlatFamilyAudit'],source_rows=rows,context_sha256=sha(a.context),compiler_sha256=COMPILER_SHA,generic_dependencies=c['generic_dependencies'],controller_sha256=sha(Path(__file__)),application_object_fallback=False,memory_limit_bytes=a.memory_gib*2**30,host_resource_probe=dict(memory=mem,disk_total=disk.total,disk_free=disk.free)))
    (a.run/'controller.py').write_bytes(Path(__file__).read_bytes());env=dict(os.environ,LEAN_PATH=str(a.run/'objects')+':'+c['generic_lean_path'],PYTHONDONTWRITEBYTECODE='1');started=time.monotonic();commands=[];peak=0
    for r in rows:
        n=r['module'];obj=a.run/'objects'/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);out=a.run/'logs'/(n+'.stdout');err=a.run/'logs'/(n+'.stderr');tm=a.run/'logs'/(n+'.time')
        cmd=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as='+str(a.memory_gib*2**30),'--stack='+str(256*2**20),'--',c['compiler'],'-j2','--root='+str(a.run/'source'),'-o',str(obj),r['snapshot']];t=time.monotonic()
        with out.open('xb')as o,err.open('xb')as e:child=subprocess.run(cmd,cwd=a.run/'source',env=env,stdout=o,stderr=e)
        rc=dict(module=n,command=cmd,exitcode=child.returncode,seconds=time.monotonic()-t,stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(tm));commands.append(rc);diagnostics=out.read_text()+err.read_text()
        if child.returncode or any(x in diagnostics for x in ['PANIC','error:','sorryAx'])or not obj.is_file():
            atomic(a.run/'FAILED.json',dict(status='FAILED',commands=commands));raise ValueError('source-cold compilation failed: '+n)
        for l in tm.read_text().splitlines():
            if 'Maximum resident set size (kbytes):'in l:peak=max(peak,int(l.rsplit(':',1)[1])*1024)
        rc['object_sha256']=sha(obj);atomic(a.run/(n+'.COMPILED.json'),rc);print('PASS',n,flush=True)
    text=(a.run/'logs/AnalyticFlatFamilyAudit.stdout').read_text();need('FLAT_FAMILY_AUDIT_PASS roots=22'in text,'typed/closure audit gate absent');need(text.count('FLAT_FAMILY_AXIOMS ')==22,'axiom audit coverage differs')
    for r in rows:need(sha(Path(r['origin']))==sha(Path(r['snapshot']))==r['source_sha256'],'source changed during replay')
    atomic(a.run/'RESULT.json',dict(status='PASS_SOURCE_COLD_KERNEL_ONLY_ANALYTIC_ANT',roots=['AnalyticFlatFamilyAudit'],modules=len(rows),commands=commands,seconds=time.monotonic()-started,max_process_rss_bytes=peak,oom_events=0,source_cold=True,kernel_only_analytic=True,source_first_PV_complete=False,actual_ANT_consumer_complete=True,explicit_inputs=['SourceBRFourierNormFive','SourceBRUniformPopulationQ1','RiemannHypothesis'],scratch_bytes=sum(p.stat().st_size for p in a.run.rglob('*')if p.is_file())));print('PASS complete general flat-family kernel-only analytic ANT; not PV',flush=True)
if __name__=='__main__':main()
