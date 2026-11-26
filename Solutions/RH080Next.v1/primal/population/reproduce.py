#!/usr/bin/env python3
"""Regenerate two actual C/AST fixtures, run C, compile full mathematical consumers.

Only pinned generic Mathlib package objects may be reused. Every application,
syntax checker, execution, numerical, Fourier and ANT proof source is rebuilt.
No official Comparator receipt is created by this supplemental replay.
"""
import argparse,concurrent.futures,contextlib,hashlib,importlib.util,io,json,os,re,shutil,subprocess,threading,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
PRIMAL=HERE.parent
REPO=HERE.parents[3]
NEXT=REPO/'Solutions/RH080Next.v1'
STUDY=REPO/'Solutions/RH080Study.v1'
def need(v,m):
 if not v:raise RuntimeError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def available():return int(next(s.split()[1]for s in Path('/proc/meminfo').read_text().splitlines()if s.startswith('MemAvailable:')))*1024
def tree_rss(pid):
 todo=[pid];seen=set();rss=0
 while todo:
  p=todo.pop()
  if p in seen:continue
  seen.add(p)
  try:
   status=(Path('/proc')/str(p)/'status').read_text();rss+=sum(int(s.split()[1])*1024 for s in status.splitlines()if s.startswith('VmRSS:'))
   for t in (Path('/proc')/str(p)/'task').iterdir():
    try:todo += [int(x)for x in (t/'children').read_text().split()]
    except(FileNotFoundError,ProcessLookupError):pass
  except(FileNotFoundError,ProcessLookupError):pass
 return rss

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--workers',type=int,choices=[1,2,3,4],default=2);ap.add_argument('--worker-memory-gib',type=int,choices=[32,64],default=64);a=ap.parse_args();out=a.out.resolve();need(not out.exists(),'Fresh output required');out.mkdir(parents=True)
 c=json.loads(a.context.read_text());pins=json.loads((STUDY/'primal56_fourier/DEPENDENCY_PINS.json').read_text());ch=sha(Path(__file__));cxh=sha(a.context)
 need(sha(Path(c['compiler']))==c['compiler_sha256']==pins['compiler_sha256'],'Compiler differs');need(c['generic_dependencies']==pins['generic_dependencies'],'Generic pins differ')
 for lib,dep in zip(c['generic_lean_path'].split(':'),pins['generic_dependencies'],strict=True):
  package=Path(lib).parents[3];need(package.name==dep['name'],'Generic library order differs');need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=package,text=True).strip()==dep['revision'],'Generic package revision differs');need(not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=package,text=True),'Generic tracked sources dirty')
 allowance=a.workers*a.worker_memory_gib*2**30;need(allowance<=300*2**30,'Per-run allowance exceeds300 GiB');need(available()>=256*2**30+allowance,'Host reserve unavailable');need(shutil.disk_usage(out).free>=2**40,'Independent free disk below1 TiB')
 pv=NEXT/'pv';regen=out/'regenerated';regen.mkdir();native_rows=[];regeneration_rows=[];cc=shutil.which('gcc');need(cc is not None,'gcc required')
 for prefix,packet,program,namespace in [('Population','population_m8_r2.json','population_norm.c','PopulationPV'),('FlatPopulation','flat_m8_r2.json','flat_population_norm.c','FlatPopulationPV')]:
  work=regen/prefix;work.mkdir();(work/'lean').mkdir();(work/'population_m8_r2.json').write_bytes((pv/packet).read_bytes())
  for n in ['WindowSource.lean','WindowExecution.lean']:(work/'lean'/n).write_bytes((pv/'lean'/n).read_bytes())
  spec=importlib.util.spec_from_file_location('untrusted_candidate_'+prefix,pv/'generate_population.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);module.HERE=work
  with contextlib.redirect_stdout(io.StringIO()):module.main()
  generated=work/'population_norm.c';need(generated.read_bytes()==(pv/program).read_bytes(),'C regeneration differs '+prefix)
  for suffix in ['AST','Source','Execution']:
   text=(work/'lean'/('Population'+suffix+'.lean')).read_text()
   if prefix=='FlatPopulation':text=text.replace('PopulationAST','FlatPopulationAST').replace('RH080Next.PopulationPV','RH080Next.FlatPopulationPV')
   expected=pv/'lean'/(prefix+suffix+'.lean');need(text.encode()==expected.read_bytes(),'AST/source regeneration differs '+str(expected));regeneration_rows.append(dict(file=str(expected.relative_to(REPO)),sha256=sha(expected)))
  sourceproof=(pv/'lean'/(prefix+'Source.lean')).read_text();match=re.search(r'def sourceChars : List Char := \[(.*?)\]\ndef source : String := String.ofList sourceChars',sourceproof,re.S);need(match is not None,'Missing exact source text fixture');charlist=match.group(1);tokens=re.findall(r'Char.ofNat (\d+)',charlist);need(', '.join('Char.ofNat '+x for x in tokens)==charlist,'Nonliteral source fixture');need(bytes(int(x)for x in tokens)==generated.read_bytes(),'Source fixture bytes differ from actual C')
  binary=work/'program';command=[cc,'-std=c11','-O2','-Wall','-Wextra','-Werror',str(generated),'-o',str(binary)];p=subprocess.run(command,capture_output=True);need(p.returncode==0,'Native C compilation failed');t=time.monotonic();p=subprocess.run([str(binary)],capture_output=True,text=True);need(p.returncode==0,'Native C execution failed');expected={'Population':'887721072633027910\n','FlatPopulation':'1120475208606944546\n'}[prefix];need(p.stdout==expected,'Actual C output differs from formally proved output');native_rows.append(dict(program=program,source_sha256=sha(generated),compiler=str(Path(cc).resolve()),compiler_sha256=sha(Path(cc).resolve()),compiler_version=subprocess.check_output([cc,'--version'],text=True),command=command,executable_sha256=sha(binary),stdout=p.stdout,seconds=time.monotonic()-t,mathematical_output_not_assumed=True))
 (out/'NATIVE_AND_REGENERATION.json').write_text(json.dumps(dict(status='PASS_ACTUAL_C_REGENERATION_EXECUTION_AND_LEAN_FIXTURE_BYTE_ASSOCIATION',programs=native_rows,artifacts=regeneration_rows),indent=2)+'\n')
 roots=[REPO,HERE,PRIMAL,NEXT/'explicit',pv/'lean',STUDY/'sine',STUDY/'pv/lean',REPO/'Solutions/CH2.v6',REPO/'Solutions/RHOnePrimeEvolution.v1/gaussian_gap']
 mappings={'CanonicalAffineSolution':REPO/'Solutions/AffineFourierPrograms.v1/Solution.lean','CanonicalWeightedSolution':REPO/'Solutions/RHWeightedPopulation.v1/Solution.lean'}
 seen=set();ordered=[];deps={}
 def generic(m):return m.startswith(('Mathlib','Lean.','Std.','Init.'))or m in ['Lean','Std','Init']
 def visit(m):
  if generic(m)or m in seen:return
  seen.add(m);candidates=[mappings.get(m)]+[r/(m.replace('.','/')+'.lean')for r in roots];source=next((p for p in candidates if p and p.is_file()),None);need(source is not None,'Missing source '+m);imports=[]
  for line in source.read_text().splitlines():
   if line.startswith('import '):imports+=line[7:].split('--',1)[0].split()
  deps[m]=[x for x in imports if not generic(x)]
  for x in imports:visit(x)
  ordered.append((m,source))
 for root in ['PopulationCanonicalAudit','PopulationMutations','CanonicalAffineSolution','CanonicalWeightedSolution']:visit(root)
 source_root=out/'source';objects=out/'objects';logs=out/'logs'
 for p in [source_root,objects,logs]:p.mkdir()
 rows=[]
 for m,origin in ordered:
  target=source_root/(m.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(origin.read_bytes());rows.append(dict(module=m,origin=str(origin),source_sha256=sha(origin),imports=deps[m]))
 plan=dict(status='FROZEN_FULL_SOURCE_COLD_NUMERICAL_FOURIER_ANT_CLOSURE',compiler=c['compiler'],compiler_sha256=c['compiler_sha256'],generic_dependencies=c['generic_dependencies'],generic_lean_path=c['generic_lean_path'],controller_sha256=ch,context_sha256=cxh,modules=rows,workers=a.workers,per_process_AS_bytes=a.worker_memory_gib*2**30,aggregate_AS_allowance_bytes=allowance,admission_MemAvailable_bytes=available(),host_reserve_bytes=256*2**30,application_object_fallback=False)
 (out/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n');(out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes());env=dict(os.environ,LEAN_PATH=str(objects)+':'+c['generic_lean_path']);start=time.monotonic();stop=threading.Event();samples=[]
 def sample():
  while not stop.is_set():samples.append(dict(seconds=time.monotonic()-start,RSS_bytes=tree_rss(os.getpid()),MemAvailable_bytes=available()));stop.wait(.5)
 thread=threading.Thread(target=sample,daemon=True);thread.start()
 def compile(row):
  m=row['module'];src=source_root/(m.replace('.','/')+'.lean');obj=objects/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);stem=m.replace('.','_');cmd=['/usr/bin/prlimit','--as='+str(a.worker_memory_gib*2**30),'--','/usr/bin/time','-v',c['compiler'],'-j1','--root='+str(source_root),'-o',str(obj),str(src)];t=time.monotonic()
  with (logs/(stem+'.stdout')).open('wb')as o,(logs/(stem+'.stderr')).open('wb')as e:r=subprocess.run(cmd,env=env,stdout=o,stderr=e)
  return dict(module=m,returncode=r.returncode,seconds=time.monotonic()-t,command=cmd,source_sha256=sha(src),object_sha256=sha(obj)if obj.exists()else None,stdout_sha256=sha(logs/(stem+'.stdout')),stderr_sha256=sha(logs/(stem+'.stderr')))
 remaining={r['module']:r for r in rows};running={};done=set();results=[];failed=None
 try:
  with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers)as pool:
   while remaining or running:
    if failed is None:
     for row in [r for r in remaining.values()if set(r['imports'])<=done]:
      if len(running)>=a.workers:break
      need(available()>=256*2**30,'Host reserve fell below256 GiB');running[pool.submit(compile,row)]=row['module'];del remaining[row['module']]
    need(running or failed is not None,'Dependency scheduler stalled')
    if not running:break
    completed,_=concurrent.futures.wait(running,timeout=30,return_when=concurrent.futures.FIRST_COMPLETED)
    for f in completed:
     m=running.pop(f);r=f.result();results.append(r)
     if r['returncode']:failed=r;(out/'FAILED.json').write_text(json.dumps(r,indent=2)+'\n')
     else:done.add(m)
     print(m,'PASS'if not r['returncode']else'FAIL',flush=True);(out/'PROGRESS.json').write_text(json.dumps(dict(compiled=len(done),required=len(rows),running=list(running.values()),last=m,failed=failed is not None))+'\n')
 finally:
  stop.set();thread.join();(out/'RESOURCES.json').write_text(json.dumps(dict(interval_seconds=.5,exact_aggregate_peak_not_measured=True,samples=samples),indent=2)+'\n')
 need(failed is None,'Compilation rejected '+str(failed));need(len(done)==len(rows),'Incomplete source closure')
 allowed={'propext','Classical.choice','Quot.sound'}
 for row in rows:
  m=row['module'];src=source_root/(m.replace('.','/')+'.lean');need(sha(src)==row['source_sha256']==sha(Path(row['origin'])),'Source changed '+m);stdout=(logs/(m.replace('.','_')+'.stdout')).read_text();printed=re.findall(r'depends on axioms: \[([^\]]*)\]',stdout);none=len(re.findall(r'does not depend on any axioms',stdout));need(len(printed)+none==src.read_text().count('#print axioms'),'Incomplete printed audit '+m);need(all({x.strip()for x in ax.split(',')if x.strip()}<=allowed for ax in printed),'Forbidden axiom '+m)
 audit=(logs/'PopulationCanonicalAudit.stdout').read_text()
 for marker in ['POPULATION_CANONICAL_AUDIT_PASS roots=18 exact_inputs=2 exact_sources=2','POPULATION_CANONICAL_SOURCE_CLOSURE_PASS','POPULATION_CANONICAL_CONTROL_CLOSURE_PASS']:need(marker in audit,'Missing actual consumer audit '+marker)
 need(sha(Path(__file__))==ch and sha(a.context)==cxh,'Controller/context changed');rss=[int(x)for p in logs.glob('*.stderr')for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())]
 result=dict(status='PASS_COMPLETE_SOURCE_FIRST_NUMERICAL_FOURIER_EVENTUAL_PRIME_POPULATION_AND_MATCHED_CONTROL',modules=len(rows),newly_compiled_modules=len(results),full_source_cold=True,application_object_fallback=False,seconds=time.monotonic()-start,maximum_recorded_per_process_GNU_RSS_kib=max(rss),sampled_aggregate_RSS_max_bytes=max(s['RSS_bytes']for s in samples),minimum_sampled_MemAvailable_bytes=min(s['MemAvailable_bytes']for s in samples),exact_aggregate_peak_not_measured=True,actual_SIGKILL_events=sum(r['returncode']in[-9,137]for r in results),bad_alloc_events=sum('bad_alloc'in p.read_text()for p in logs.glob('*.stderr')),disk_bytes=sum(p.stat().st_size for p in out.rglob('*')if p.is_file()),disk_peak_not_measured=True,standard_axioms=sorted(allowed),analytic_inputs=['BRFourierInput.v1.norm_identity','BRFourierInput.v1.uniform_population_q1','ordinaryRH'],explicit_onset=False,official_Comparator=False,PV_causal_mathematical_advantage_over_matched_control=False,plan_sha256=sha(out/'PLAN.json'),native_receipt_sha256=sha(out/'NATIVE_AND_REGENERATION.json'),commands=results)
 tmp=out/'RESULT.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');os.link(tmp,out/'RESULT.json');tmp.unlink();print(json.dumps({k:v for k,v in result.items()if k!='commands'}))
if __name__=='__main__':main()
