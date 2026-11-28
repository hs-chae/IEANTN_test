#!/usr/bin/env python3
"""Compile new application modules once against source/receipt-associated dependencies.
Canonical-node extension of compile_verified_batch: additionally resolves the
actual core node sources and the pinned finite canonical helper directory.
Hardlinks frozen accepted transitive objects into a fresh import root; this is a source-associated batch,
not a fresh source-cold replay or completed ANT source-first PV acceptance.
"""
from __future__ import annotations
import argparse,hashlib,json,os,subprocess,time
from pathlib import Path
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'}
def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
      while chunk:=f.read(8*1024*1024):h.update(chunk)
    return h.hexdigest()
def read_json(p):
    def pairs(items):
      d={}
      for k,v in items:need(k not in d,'duplicate JSON key '+k);d[k]=v
      return d
    def bad(x):raise ValueError('nonfinite JSON '+x)
    return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=bad)
def atomic(p,value):
    need(not p.exists(),'fresh atomic receipt required');t=p.with_name('.'+p.name+'.tmp')
    with t.open('x') as f:json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(t,p)
    finally:t.unlink()
def imports(p):return [n for l in p.read_text().splitlines() if l.startswith('import ') for n in l[7:].split('--',1)[0].split()]

AS_POLICY = "EXPLICIT_RLIM_INFINITY_WITH_SEPARATE_PHYSICAL_CGROUP"
PHYSICAL_BYTES = 300 * 2**30

def physical_guard():
 import resource
 rows = Path('/proc/self/cgroup').read_text().splitlines()
 unified = [row[3:] for row in rows if row.startswith('0::')]
 need(len(unified) == 1, 'One actual unified owned cgroup required')
 relative = Path(unified[0])
 need(relative.is_absolute() and '..' not in relative.parts and
      relative.name.endswith('.service'), 'Owned service cgroup required')
 cg = Path('/sys/fs/cgroup') / str(relative).lstrip('/')
 need((cg/'memory.max').read_text().strip() == str(PHYSICAL_BYTES),
      'Actual physical300GiB owned cgroup required')
 need((cg/'memory.swap.max').read_text().strip() == '0', 'No-swap owned cgroup required')
 limits = resource.getrlimit(resource.RLIMIT_AS)
 need(limits == (resource.RLIM_INFINITY, resource.RLIM_INFINITY),
      'Explicit unlimited parent virtual AS required; physical bound remains separate')
 events = {}
 for row in (cg/'memory.events').read_text().splitlines():
  key, value = row.split()
  need(key not in events and value.isdigit(), 'Strict actual memory event counters required')
  events[key] = int(value)
 need('oom' in events and 'oom_kill' in events, 'Actual owned OOM counters absent')
 return dict(cgroup=str(relative), physical_memory_max_bytes=PHYSICAL_BYTES,
             memory_swap_max_bytes=0, worker_virtual_as_policy=AS_POLICY,
             per_compiler_AS_bytes=None, memory_events=events)

def final_physical_guard(before):
 after = physical_guard()
 need(after['cgroup'] == before['cgroup'], 'Owned physical cgroup changed')
 return after

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',required=True,type=Path);ap.add_argument('--bank',required=True,action='append',type=Path);ap.add_argument('--root',required=True,action='append');ap.add_argument('--run',required=True,type=Path);ap.add_argument('--memory-gib',type=int,required=True);ap.add_argument('--worker-virtual-as',choices=['unlimited'],required=True);a=ap.parse_args();physical_before=physical_guard()
    need(not a.run.exists(),'fresh experiment-owned run required');need(a.memory_gib==300,'physical planning declaration must match owned300GiB')
    mem={l.split(':')[0]:int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()};need(mem['MemAvailable']>=(a.memory_gib+256)*2**30,'insufficient available RAM after host reserve')
    ctx=read_json(a.context);need(sha(Path(ctx['compiler']))==ctx['compiler_sha256'],'pinned compiler changed');context_sha=sha(a.context);index={}
    for bank in a.bank:
      plan=read_json(bank/'PLAN.json');need(plan['context_sha256']==context_sha,'dependency context differs')
      rows=plan.get('source_rows',[dict(module=plan.get('module'),origin=plan.get('source_origin'),snapshot=str(bank/'source'/(plan.get('module','').replace('.','/')+'.lean')),source_sha256=plan.get('source_sha256'))])
      for r in rows:
        n=r['module'];need(isinstance(n,str)and bool(n),'Unsupported bank schema: use source/receipt format export');rp=bank/(n+'.COMPILED.json');rp=rp if rp.is_file() else bank/'RESULT.json'
        if not rp.is_file():continue
        receipt=read_json(rp);obj=bank/'objects'/(n.replace('.','/')+'.olean')
        if receipt.get('module')==n and type(receipt.get('exitcode'))is int and receipt['exitcode']==0 and obj.is_file():index.setdefault(n,[]).append((r,rp,receipt,obj))
      for item in plan.get('accepted_dependencies',[]):
        need(all(k in item for k in ['source_origin','snapshot','receipt','receipt_sha256']),'incomplete transitive provenance')
        rp=Path(item['receipt']);need(rp.is_file() and sha(rp)==item['receipt_sha256'],'transitive compiler receipt changed');receipt=read_json(rp);obj=bank/'objects'/(item['module'].replace('.','/')+'.olean')
        need(type(receipt.get('exitcode'))is int and receipt['exitcode']==0 and obj.is_file() and sha(obj)==item['object_sha256']==receipt['object_sha256'],'transitive copied proof object changed')
        r=dict(module=item['module'],origin=item['source_origin'],snapshot=item['snapshot'],source_sha256=item['source_sha256']);index.setdefault(item['module'],[]).append((r,rp,receipt,obj))
    project=Path(__file__).resolve().parent.parent
    source_bases=[project/'pv/lean',project/'explicit',project/'primal',project/'dual',project/'primal/finite',project/'primal/population',project.parents[1]]
    seen=set();active=set();fresh=[];accepted=[]
    def visit(n,force=False):
      if n in seen or n.split('.')[0] in GENERIC:return
      need(n not in active,'application import cycle');active.add(n);found=None
      if not force:
        for r,rp,receipt,obj in index.get(n,[]):
          origin=Path(r['origin']);snapshot=Path(r['snapshot'])
          if origin.is_file() and snapshot.is_file() and sha(origin)==sha(snapshot)==r['source_sha256'] and sha(obj)==receipt['object_sha256']:
            found=(r,rp,receipt,obj);break
      if found:
        r,rp,receipt,obj=found
        for child in imports(Path(r['origin'])):visit(child)
        accepted.append(dict(module=n,source_origin=r['origin'],source_sha256=r['source_sha256'],snapshot=r['snapshot'],object_sha256=sha(obj),receipt=str(rp),receipt_sha256=sha(rp),object_origin=str(obj)))
      else:
        candidates=[p for b in source_bases if (p:=b/(n.replace('.','/')+'.lean')).is_file()];need(len(candidates)==1,'source must resolve uniquely: '+n);origin=candidates[0]
        for child in imports(origin):visit(child)
        fresh.append(dict(module=n,origin=str(origin),source_sha256=sha(origin),imports=imports(origin)))
      active.remove(n);seen.add(n)
    for n in a.root:visit(n,True)
    need(fresh,'new selected proof modules required');a.run.mkdir(parents=True)
    for child in ['source','objects','logs']:(a.run/child).mkdir()
    for r in accepted:
      target=a.run/'objects'/(r['module'].replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True);origin=Path(r['object_origin']);need(origin.stat().st_dev==target.parent.stat().st_dev,'Frozen proof bank must be on same filesystem for thin overlay');os.link(origin,target);need(sha(target)==r['object_sha256'],'hardlinked dependency differs')
    for r in fresh:
      target=a.run/'source'/(r['module'].replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(Path(r['origin']).read_bytes());r['snapshot']=str(target);need(sha(target)==r['source_sha256'],'fresh snapshot differs')
    (a.run/'controller.py').write_bytes(Path(__file__).read_bytes())
    atomic(a.run/'PLAN.json',dict(status='FROZEN_SOURCE_ASSOCIATED_BATCH_PLAN_NOT_WHOLE_PV',roots=a.root,source_rows=fresh,accepted_dependencies=accepted,context_sha256=context_sha,controller_sha256=sha(Path(__file__)),application_object_fallback=False,source_cold=False,physical_before=physical_before,worker_virtual_as_policy=AS_POLICY,per_compiler_AS_bytes=None,physical_memory_max_bytes=PHYSICAL_BYTES,accepted_dependency_storage='hardlinks to frozen source-associated proof objects'))
    env=dict(os.environ,LEAN_PATH=str(a.run/'objects')+':'+ctx['generic_lean_path'],PYTHONDONTWRITEBYTECODE='1');began=time.monotonic();commands=[]
    for r in fresh:
      n=r['module'];obj=a.run/'objects'/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);out=a.run/'logs'/(n+'.stdout');err=a.run/'logs'/(n+'.stderr');tm=a.run/'logs'/(n+'.time')
      cmd=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as=unlimited','--stack='+str(256*2**20),'--',ctx['compiler'],'-j2','--root='+str(a.run/'source'),'-o',str(obj),r['snapshot']];t=time.monotonic()
      with out.open('xb') as o,err.open('xb') as e:child=subprocess.run(cmd,cwd=a.run/'source',env=env,stdout=o,stderr=e)
      receipt=dict(module=n,command=cmd,exitcode=child.returncode,seconds=time.monotonic()-t,stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(tm));commands.append(receipt)
      diagnostics=out.read_text()+err.read_text()
      if child.returncode or any(bad in diagnostics for bad in ['PANIC','error:','sorryAx']) or not obj.is_file():
        atomic(a.run/'FAILED.json',dict(status='FAILED_SOURCE_ASSOCIATED_BATCH',commands=commands));raise ValueError('compiler/strict diagnostics failed: '+n)
      receipt['object_sha256']=sha(obj);atomic(a.run/(n+'.COMPILED.json'),receipt);print('PASS',n,flush=True)
    for r in fresh:need(sha(Path(r['origin']))==r['source_sha256'],'source changed during batch')
    for r in accepted:need(sha(Path(r['source_origin']))==r['source_sha256'] and sha(Path(r['snapshot']))==r['source_sha256'] and sha(Path(r['receipt']))==r['receipt_sha256'] and sha(a.run/'objects'/(r['module'].replace('.','/')+'.olean'))==r['object_sha256'],'accepted dependency changed during batch')
    atomic(a.run/'RESULT.json',dict(status='PASS_SOURCE_ASSOCIATED_BATCH_MODULES_ONLY',roots=a.root,modules=len(fresh),accepted_modules=len(accepted),commands=commands,seconds=time.monotonic()-began,source_cold=False,source_first_PV_complete=False,final_ANT_connection_pending=True,physical_before=physical_before,physical_after=final_physical_guard(physical_before),worker_virtual_as_policy=AS_POLICY,per_compiler_AS_bytes=None,physical_memory_max_bytes=PHYSICAL_BYTES,oom_events_measured='actual owned cgroup before/after in physical_before/physical_after',all_recorded_compiler_exitcodes=[r['exitcode']for r in commands],accepted_dependency_storage='hardlinked, exact hashes revalidated',reused_dependency_logical_bytes=sum(Path(r['object_origin']).stat().st_size for r in accepted)));print('PASS source-associated batch; final ANT connection pending',flush=True)
if __name__=='__main__':main()
