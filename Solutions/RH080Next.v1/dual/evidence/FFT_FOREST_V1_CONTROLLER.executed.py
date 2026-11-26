"""Fresh generic-context kernel replay. This validates a numerical trace, not source-first PV."""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess,sys,time,threading
R=Path(__file__).resolve().parents[3];S=R/'Solutions/RH080Next.v1'
from reproduce_dual import context,publish,need,sha
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--run',type=Path,required=True);p.add_argument('--workers',type=int,default=4);o=p.parse_args();need(1<=o.workers<=16,'Worker bound');need(not o.run.exists(),'Fresh run required')
c=context(o.context,R);candidate=json.loads((o.candidate/'PLAN.json').read_text());need(candidate['status']=='UNTRUSTED_EXACT_INTEGER_FOREST_NOT_PROOF_NOT_PV','Unexpected candidate');stages=candidate['stages'];need(type(stages) is int and 10<=stages<=17,'Stage range');need(candidate['namespace']=='FapForest'+str(stages),'Wrong numerical scope')
o.run.mkdir();frozen=o.run/'sources';frozen.mkdir();bank=o.run/'objects';bank.mkdir();driver=Path(__file__);shutil.copyfile(driver,o.run/'driver.executed.py');producer=S/'dual/produce_fft_forest_certificate.py';need(sha(producer)==candidate['producer_sha256'],'Producer identity');shutil.copyfile(producer,o.run/'producer.executed.py');shutil.copyfile(o.candidate/'PLAN.json',o.run/'CANDIDATE.json')
for row in candidate['payloads']+candidate['lean_sources']:
 name=row['file'];need(Path(name).name==name and name not in ('','.', '..'),'Payload path');src=o.candidate/name;need(sha(src)==row['sha256'],'Candidate bytes mismatch '+name);shutil.copyfile(src,frozen/name)
base=['FapData','FFTPairedIntModel','FFTTraceChecker','FFTForestTrace','FFTUntrustedData'];sources=[]
for name in base:
 src=S/('pv/lean' if name=='FapData' else 'dual')/(name+'.lean');shutil.copyfile(src,frozen/src.name)
for src in sorted(frozen.iterdir()):sources.append({'file':src.name,'sha256':sha(src),'bytes':src.stat().st_size})
plan={'status':'FROZEN_FULL_INTEGER_FFT_TRACE_NOT_SOURCE_PV','driver_sha256':sha(driver),'candidate_plan_sha256':sha(o.candidate/'PLAN.json'),'sources':sources,'context':c,'context_sha256':sha(o.context),'workers':o.workers,'stages':stages,'candidate':candidate};publish(o.run/'PLAN.json',plan);env=dict(os.environ,LEAN_PATH=str(bank)+':'+c['generic_lean_path']);start=time.monotonic();done=[];lock=threading.Lock()
def compile_one(name):
 src=frozen/(name+'.lean');cmd=[c['compiler'],'-j1','-R',str(frozen),'-o',str(bank/(name+'.olean')),str(src)];t=time.monotonic();tm=o.run/(name+'.time');out=o.run/(name+'.stdout');err=o.run/(name+'.stderr')
 with out.open('x') as f,err.open('x') as g:r=subprocess.run(['/usr/bin/time','-v','-o',str(tm),*cmd],env=env,stdout=f,stderr=g)
 text=tm.read_text();peak=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',text);row={'module':name,'returncode':r.returncode,'seconds':time.monotonic()-t,'peak_RSS_KiB':int(peak[1]) if peak else None,'source_sha256':sha(src),'command':cmd,'time_sha256':sha(tm),'stdout_sha256':sha(out),'stderr_sha256':sha(err)};publish(o.run/(name+'.COMPILED.json'),row)
 with lock:done.append(row);print(json.dumps({k:row[k]for k in ('module','returncode','seconds','peak_RSS_KiB')}),flush=True)
 need(r.returncode==0,'Compile failed '+name)
 logs=out.read_text()+'\n'+err.read_text()
 need(re.search(r'PANIC|error(?:\([^)]*\))?:',logs) is None,'Compiler diagnostic despite exit '+str(r.returncode)+' in '+name)
 need((bank/(name+'.olean')).is_file(),'Missing proof object '+name)
 return row
try:
 for name in base:compile_one(name)
 def batch(names):
  with concurrent.futures.ThreadPoolExecutor(max_workers=o.workers)as ex:
   results=list(ex.map(compile_one,names))
  return results
 batch(['ForestTables']+[f'ForestData{s:02}'for s in range(1,stages+1)])
 batch(['ForestTablesCheck']+[f'ForestCheck{s:02}'for s in range(1,stages+1)])
 compile_one('ForestFinal')
 allowed={'propext','Classical.choice','Quot.sound'};audits=[]
 expected={'ForestTablesCheck':['global_twiddle_trace']+[f'decimation{s:02}'for s in range(1,stages)],'ForestFinal':['complete_execution','numerator_checked']}
 expected.update({f'ForestCheck{s:02}':[f'layer{s:02}_trace']for s in range(1,stages+1)})
 for module,names in expected.items():
  text=(o.run/(module+'.stdout')).read_text()
  for name in names:
   full=candidate['namespace']+'.'+name;patterns=re.findall(r"'"+re.escape(full)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text);need(len(patterns)==1,'Missing/duplicate audit '+full);axes={x.strip()for x in patterns[0].split(',')if x.strip()};need(axes<=allowed,'Unapproved axiom '+full);audits.append({'root':full,'axioms':sorted(axes)})
 for row in sources:need(sha(frozen/row['file'])==row['sha256'],'Frozen source changed '+row['file'])
 need(sha(driver)==plan['driver_sha256'],'Driver changed')
 objects=[{'file':p.name,'sha256':sha(p),'bytes':p.stat().st_size}for p in sorted(bank.iterdir())if p.is_file()]
 publish(o.run/'AXIOM_AUDIT.json',{'status':'PASS','roots':audits});publish(o.run/'OBJECTS.json',objects)
 result={'status':'PASS_COMPLETE_INTEGER_FFT_TRACE_AND_LITERAL_OUTPUT_NOT_SOURCE_PV','stages':stages,'N':2**stages,'norm_numerator':candidate['norm_numerator'],'seconds':time.monotonic()-start,'max_individual_RSS_KiB':max(x['peak_RSS_KiB']or 0 for x in done),'disk_bytes':sum(x.stat().st_size for x in o.run.rglob('*')if x.is_file()),'modules':len(done),'audited_roots':len(audits),'OOM_kills':sum(1 for x in done if x['returncode']==-9),'axioms':sorted({a for r in audits for a in r['axioms']}),'plan_sha256':sha(o.run/'PLAN.json')};publish(o.run/'RESULT.json',result);print(json.dumps(result),flush=True)
except BaseException as error:
 publish(o.run/'FAILURE.json',{'status':'NO_ACCEPTANCE','error':str(error),'seconds':time.monotonic()-start,'completed':done});raise
