#!/usr/bin/env python3
"""Fresh source-frozen compilation of the complete NEW CMS frontier chain.
Generic Mathlib/LeanCert foundation objects are explicit input dependencies;
this script does not claim to rebuild those foundations or prove source616.
"""
from pathlib import Path
import argparse,hashlib,json,os,resource,re,subprocess,time
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--foundation-paths',required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
if a.out.exists():raise SystemExit('Output must be a new owned directory')
b=Path(__file__).resolve().parent;root=b.parent
modules=[('CMSKernelNumerics',root/'comparisons/CMSKernelNumerics.lean')]+[(n,b/(n+'.lean'))for n in ['CMSScalarFrontier','CMSGeometry','CMSPrimeFrontier','CMSOpenTransfer','CMSJSharper','CMSSharperUniform','CMSWholeFrontier','CMSFinalFrontier','CMSGeometrySharp','CMSTightSlab','CMSContinuousFrontier','CMSFiniteBenchmarks']]
if any(not f.is_file() for _,f in modules):raise SystemExit('Missing required source')
a.out.mkdir(parents=True);frozen=a.out/'source';obj=a.out/'objects';logs=a.out/'logs'
for x in [frozen,obj,logs]:x.mkdir()
ctx=json.loads(a.context.read_text());env=os.environ.copy();env['LEAN_PATH']=':'.join([str(obj),a.foundation_paths,*ctx['generic_libraries']]);env['LEAN_NUM_THREADS']='2'
rows=[]
for n,f in modules:(frozen/(n+'.lean')).write_bytes(f.read_bytes())
(a.out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
start=time.monotonic()
for n,f in modules:
 source=frozen/(n+'.lean');cmd=[ctx['compiler'],'-j2','--root='+str(frozen),'-o',str(obj/(n+'.olean')),str(source)];t=time.monotonic()
 run=subprocess.run(['/usr/bin/time','-v',*cmd],env=env,cwd=frozen,text=True,capture_output=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3)))
 (logs/(n+'.stdout')).write_text(run.stdout);(logs/(n+'.stderr')).write_text(run.stderr)
 audits=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",run.stdout,re.S)
 allowed={'propext','Classical.choice','Quot.sound'}
 invalid=[(name,axes)for name,axes in audits if set(map(str.strip,axes.split(',')))-allowed]
 if run.returncode or not audits or invalid:
  (a.out/'FAILURE.json').write_text(json.dumps({'module':n,'returncode':run.returncode,'invalid_audits':invalid,'command':cmd},indent=2)+'\n');raise SystemExit('Compilation/audit failed at '+n)
 rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',run.stderr)
 row={'module':n,'source':str(f),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'object_sha256':hashlib.sha256((obj/(n+'.olean')).read_bytes()).hexdigest(),'command':cmd,'seconds':time.monotonic()-t,'peak_child_RSS_KiB':int(rss.group(1))if rss else None,'audited_theorems':len(audits),'axiom_sets':{name:list(map(str.strip,axes.split(',')))for name,axes in audits},'stdout_sha256':hashlib.sha256(run.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(run.stderr.encode()).hexdigest()};rows.append(row);print(n,'PASS',round(row['seconds'],2),flush=True)
rec={'status':'PASS_FRESH_ALL13_CMS_FRONTIER_SOURCES_AND_HEADLINE_AXIOM_CLOSURES','modules':rows,'seconds':time.monotonic()-start,'LEAN_PATH':env['LEAN_PATH'],'compiler':ctx['compiler'],'compiler_sha256':hashlib.sha256(Path(ctx['compiler']).read_bytes()).hexdigest(),'context_sha256':hashlib.sha256(a.context.read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'literature_B_input':'RHOnePrime.CMSPrime.SourceCMS616; published CMS proof passage6.16; not proved fromGreen/Nico/BPT','source_first_PV':False,'generic_foundation_objects_reused':True,'claimed_mathematics':'SourceconditionalB+D: strictopen continuousendpoint uniformlyinside.8768 frome44; .8185 on[e44,e59],.8357 on[e44,e110],.8512 on[e44,e225]; originalninefinitebranches preserved','oom_events':0}
(a.out/'RESULT.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],rec['seconds'])
