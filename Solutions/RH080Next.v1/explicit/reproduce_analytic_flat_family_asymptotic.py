#!/usr/bin/env python3
"""Reproduce the full real-density flat-family population asymptotic.
Application sources compile from bytes; only pinned generic-library objects enter.
No mathematical conclusion, numerical norm cap or source program is an input.
"""
import argparse,os,subprocess,json,hashlib,time,shutil
from pathlib import Path
R=Path(__file__).resolve().parents[3]
S=R/'Solutions/RH080Next.v1'
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'}
PINS={'mathlib':'71a80585ee495fc24472fd0eaffc89d94e4fd8d6','plausible':'d9598f07b1bc701f1e3aae163d2681c1fd978793','LeanSearchClient':'ba67e212be1197b84c1f1f6299488a10a3002713','importGraph':'1681d78dd6e65e38b143f9740d829c826673807c','proofwidgets':'a8acbfd87375ff4abe14ce09db5b7664d383bc7f','aesop':'18889deb9e83ea7420ef51c160d6f88552e744e3','Qq':'507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3','batteries':'4cac2177c37f5530c4da76aa8e4307f3fc9e4dcb'}
SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
def need(v,s):
 if not v:raise ValueError(s)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic(p,d):
 need(not p.exists(),'receipt exists '+str(p));t=p.with_name('.'+p.name+'.tmp')
 with t.open('x')as f:json.dump(d,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
 try:os.link(t,p)
 finally:t.unlink()
def imports(p):return[n for l in p.read_text().splitlines()if l.startswith('import ')for n in l[7:].split('--',1)[0].split()]
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--run',type=Path,required=True);a=ap.parse_args()
 need(not a.run.exists(),'fresh run required');c=json.loads(a.context.read_text());need(sha(Path(c['compiler']))==c['compiler_sha256']==SHA,'compiler pin');need({d['name']:d['revision']for d in c['generic_dependencies']}==PINS,'generic pins')
 for e in c['generic_lean_path'].split(':'):
  repo=Path(e).resolve().parents[3];need(subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()==PINS.get(repo.name),'generic checkout '+str(repo))
 mem={l.split(':')[0]:int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()};need(mem['MemAvailable']>=(32+256)*2**30,'host reserve');need(shutil.disk_usage(a.run.parent).free>2**30,'scratch')
 bases=[S/'explicit',S/'primal',S/'dual',S/'pv/lean',R/'Solutions/CH2.v6',R]
 rows=[];seen=set();active=set()
 def visit(n):
  if n in seen or n.split('.')[0]in GENERIC:return
  need(n not in active,'cycle '+n);active.add(n)
  paths=[p for b in bases if(p:=b/(n.replace('.','/')+'.lean')).is_file()]
  need(len(paths)==1,'source uniqueness '+n);p=paths[0]
  for child in imports(p):visit(child)
  rows.append(dict(module=n,origin=str(p),source_sha256=sha(p),imports=imports(p)));active.remove(n);seen.add(n)
 visit('AnalyticFlatFamilyAsymptoticAudit');a.run.mkdir()
 for n in ['source','objects','logs']:(a.run/n).mkdir()
 (a.run/'controller.py').write_bytes(Path(__file__).read_bytes())
 for row in rows:
  p=a.run/'source'/(row['module'].replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(Path(row['origin']).read_bytes());row['snapshot']=str(p)
 atomic(a.run/'PLAN.json',dict(source_rows=rows,compiler_sha256=SHA,context_sha256=sha(a.context),generic_dependencies=c['generic_dependencies'],controller_sha256=sha(Path(__file__)),application_object_fallback=False,proof_boundary='kernel-only analytic, two explicit BR source inputs and RH; not PV',memory_limit_bytes=32*2**30,host_MemAvailable=mem['MemAvailable']))
 env=dict(os.environ,LEAN_PATH=str(a.run/'objects')+':'+c['generic_lean_path']);cmds=[];start=time.monotonic();peak=0
 for row in rows:
  n=row['module'];obj=a.run/'objects'/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);o=a.run/'logs'/(n+'.stdout');e=a.run/'logs'/(n+'.stderr');tm=a.run/'logs'/(n+'.time')
  cmd=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as='+str(32*2**30),'--stack='+str(256*2**20),'--',c['compiler'],'-j2','--root='+str(a.run/'source'),'-o',str(obj),row['snapshot']];t=time.monotonic()
  with o.open('x')as out,e.open('x')as err:r=subprocess.run(cmd,env=env,cwd=a.run/'source',stdout=out,stderr=err)
  text=o.read_text()+e.read_text();rc=dict(module=n,command=cmd,exitcode=r.returncode,seconds=time.monotonic()-t,stdout_sha256=sha(o),stderr_sha256=sha(e),time_sha256=sha(tm));cmds.append(rc)
  if r.returncode or any(t in text for t in ['error:','PANIC','sorryAx'])or not obj.is_file():
   atomic(a.run/'FAILED.json',dict(status='FAILED',commands=cmds));raise ValueError('compile '+n)
  rc['object_sha256']=sha(obj)
  for line in tm.read_text().splitlines():
   if 'Maximum resident set size (kbytes):'in line:peak=max(peak,int(line.rsplit(':',1)[1])*1024)
  print('PASS',n,flush=True)
 text=(a.run/'logs/AnalyticFlatFamilyAsymptoticAudit.stdout').read_text();need('REAL_ALPHA_ASYMPTOTIC_AUDIT_PASS roots=15'in text,'typed gate');need(text.count('REAL_ALPHA_ASYMPTOTIC_AXIOMS ')==15,'axiom population')
 for row in rows:need(sha(Path(row['origin']))==sha(Path(row['snapshot']))==row['source_sha256'],'source changed '+row['module'])
 atomic(a.run/'RESULT.json',dict(status='PASS_SOURCE_COLD_REAL_ALPHA_ASYMPTOTIC_ANALYTIC_ANT_NOT_PV',modules=len(rows),theorem_count=15,commands=cmds,seconds=time.monotonic()-start,max_compiler_rss_bytes=peak,aggregate_cgroup_peak='not measured',oom_events='not independently measured; no zero-OOM claim',source_cold=True,application_object_fallback=False,explicit_inputs=['SourceBRFourierNormFive','SourceBRUniformPopulationQ1','RiemannHypothesis'],kernel_only_analytic=True,source_first_PV=False))
 print('PASS source-cold real-alpha asymptotic analytic ANT',flush=True)
if __name__=='__main__':main()
