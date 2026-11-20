#!/usr/bin/env python3
"""Compile every full-prefix scalar block and independently type-audit the result.
This closes kernel scalar/real-enclosure/coverage leaves, never prime counts or C PV.
"""
from pathlib import Path
import argparse,concurrent.futures,datetime,hashlib,json,os,re,struct,subprocess,sys,time
S=Path(__file__).resolve().parents[1];STANDARD={'propext','Classical.choice','Quot.sound'}
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(p):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def atomic(p,v):
 q=p.with_name(p.name+'.pending');q.write_text(json.dumps(v,indent=2,allow_nan=False)+'\n');q.replace(p)
def axioms(log,names):
 result={}
 for name in names:
  xs=re.findall("'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",log,re.S);free=re.findall("'"+re.escape(name)+"' does not depend on any axioms",log);need(len(xs)+len(free)==1,'one named actual axiom audit '+name);found=[] if free else [x.strip() for x in xs[0].split(',') if x.strip()];need(len(found)==len(set(found)) and set(found)<=STANDARD,'only standard logical axioms '+name);result[name]=sorted(found)
 return result

def validate(result_path):
 d=read(result_path);need(d['status']=='ALL_SCALAR_ENCLOSURE_AND_COVERAGE_KERNEL_CHECKS_PASS_COUNTS_OPEN_NOT_C_PV','complete scalar result');need(sha(d['manifest'])==d['manifest_sha256'],'exact proposal');m=read(d['manifest']);need(len(d['records'])==len(m['modules'])+1,'every source and independent audit');need(d['rows']==m['rows'] and d['prime_counts_formally_proved_here'] is False and d['source_first_PV'] is False,'mathematical scope');expected=[x['module'] for x in m['modules']];need([x['module'] for x in d['records'][:-1]]==expected,'complete module order')
 for index,record in enumerate(d['records']):
  required=m['modules'][index].get('standard_constants',[]) if index<len(m['modules']) else [m['namespace']+'.all_scalars']
  need(record['required_constants']==required,'complete independently prescribed axiom population')
  if index<len(m['modules']):
   need(record['module']==m['modules'][index]['module'],'exact compiler module')
  else:need(record['module']==m['namespace']+'.ControllerAudit','independent controller audit')
  p=Path(record['receipt']);need(sha(p)==record['receipt_sha256'],'receipt identity');r=read(p);need(r['status']=='COMPILED' and r['returncode']==0 and r['source_unchanged_during_compile'] is True,'every actual source compile');need(sha(r['source'])==r['source_sha256']==sha(p.parent/'source.lean'),'same actual/snapshot source');need(sha(record['object'])==r['object_sha256'],'actual object');need(sha(p.parent/'stdout')==r['stdout_sha256'] and sha(p.parent/'rusage.txt')==r['rusage_sha256'],'actual stdout/resources');names=record['required_constants'];need(axioms((p.parent/'stdout').read_text(),names)==record['axioms'],'all compulsory axiom reports')
 return {'status':'READBACK_PASS','rows':d['rows'],'modules':len(m['modules']),'counts_still_open':True,'result_sha256':sha(result_path)}

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--manifest',type=Path);p.add_argument('--native-run',type=Path);p.add_argument('--out',type=Path);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');p.add_argument('--jobs',type=int,default=12);p.add_argument('--memory-gib',type=int,default=24);p.add_argument('--cpus',default=','.join(map(str,range(52,64))));p.add_argument('--allow-profile',action='store_true');p.add_argument('--check',type=Path);a=p.parse_args()
 if a.check:
  need(a.manifest is None and a.out is None and a.native_run is None,'separate read-only checking');print(json.dumps(validate(a.check)));return
 need(a.manifest is not None and a.native_run is not None and a.out is not None,'manifest/native-run/fresh output required');need(1<=a.jobs<=32 and 1<=a.memory_gib<=300 and a.jobs*a.memory_gib<=300,'combined worker allowance');cpus=[int(x) for x in a.cpus.split(',')];need(len(cpus)==len(set(cpus)) and len(cpus)>=a.jobs and set(cpus)<=os.sched_getaffinity(0),'distinct available CPUs');mem=int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024;need(mem>=1024**4 and mem>=(512+a.jobs*a.memory_gib)*1024**3,'genuinely available RAM and host reserve')
 m=read(a.manifest);need(m['schema']=='RAMANUJAN_FULL_SCALARS_PROPOSAL_V1' and m['status']=='UNTRUSTED_SCALAR_PROPOSAL_ALL_KERNEL_CHECKS_REQUIRED','exact proposal');need(m['prime_counts_formally_proved_here'] is False and m['source_first_PV'] is False,'no count or PV promotion');need(a.allow_profile or (m['full_locked_prefix'] is True and m['rows']==1755663 and m['stop']==1490000000001),'entire fixed full prefix or explicit profile');need(m['begin']==38358837683 and re.fullmatch(r'RamanujanPV\.[A-Za-z][A-Za-z0-9_]*',m['namespace']) is not None,'exact start and namespace');native=read(a.native_run);need(sha(a.native_run)==m['native_run_sha256'] and native['begin']==38358837683 and native['end_inclusive']==1490000000000 and native['mode']=='actual','original native input identity')
 root=Path(m['source_root']);names=[x['module'] for x in m['modules']];need(len(names)==len(set(names)) and set(root.rglob('*.lean'))=={Path(x['source']) for x in m['modules']},'complete written source universe');need(len(m['modules'])==2*len(m['blocks'])+1,'exact data/check/final geometry')
 for x in m['modules']:need(sha(x['source'])==x['source_sha256'],'immutable current source')
 previous=m['begin'];total=0
 for b in m['blocks']:need(b['start']==previous and b['start']<b['stop'] and b['count']>0,'every exact block boundary');previous=b['stop'];total+=b['count']
 need(previous==m['stop'] and total==m['rows'],'entire row and boundary coverage')
 # Independent join of every actual literal against the original binary stream;
 # preorder pivots must be the balanced offsets, so leaf order is also lookup order.
 def native_rows():
  remaining=m['rows']
  for row in m['native_binary_inputs']:
   ref=native['records'][row['chunk']];file=Path(row['path']);need(sha(file)==ref['certificate_sha256']==row['sha256'],'original binary hash at readback')
   with file.open('rb') as f:
    for buf in iter(lambda:f.read(56*4096),b''):
     need(len(buf)%56==0,'whole binary records')
     for values in struct.iter_unpack('<7Q',buf):
      if remaining==0:return
      remaining-=1;yield values
  need(remaining==0,'all required original binary rows available')
 original=iter(native_rows());checked_rows=0
 for block in m['blocks']:
  dm=next(x for x in m['modules'] if x['module']==block['data_module']);text=Path(dm['source']).read_text();leaves=re.findall(r'\(\.leaf ⟨⟨([0-9,]+)⟩,([0-9]+)⟩\)',text);need(len(leaves)==block['count'],'all actual data leaves')
  for fields,k in leaves:
   row=tuple(map(int,fields.split(',')));need(row==next(original) and int(k)==row[0].bit_length()-1,'every original seven-word row and normalization exponent');checked_rows+=1
  expected_pivots=[]
  def pivots(lo,hi):
   if hi-lo==1:return
   mid=(lo+hi)//2;expected_pivots.append(mid);pivots(lo,mid);pivots(mid,hi)
  pivots(0,block['count']);need(list(map(int,re.findall(r'\(\.branch ([0-9]+)',text)))==expected_pivots,'all lookup tree pivots and leaf positions')
 need(checked_rows==m['rows'] and next(original,None) is None,'complete independent binary-to-source join')
 context=read(a.context);objects=Path(context['new_application_object_root']);out=a.out.resolve();need(not out.exists() and out.is_relative_to(objects.parent),'fresh owned output');out.mkdir(parents=True);(out/'logs').mkdir();started=time.monotonic();results={}
 def compile_module(x,cpu,limit):
  label=x['module'];command=[sys.executable,str(S/'scripts/compile_lean_context.py'),label,'--context',str(a.context.resolve()),'--source-root',str(x.get('source_root',root)),'--audit-root',str(out/'audit'),'--cpus',str(cpu),'--memory-gib',str(limit)]
  with (out/'logs'/(label+'.stdout')).open('w') as stdout,(out/'logs'/(label+'.stderr')).open('w') as stderr:run=subprocess.run(command,stdout=stdout,stderr=stderr)
  need(run.returncode==0,'actual compiler failure '+label);rp=out/'audit'/label/'1/RUN.json';r=read(rp);need(r['status']=='COMPILED' and r['source_sha256']==x['source_sha256'],'exact current compiler result');required=x.get('standard_constants',[]);value=dict(module=label,receipt=str(rp),receipt_sha256=sha(rp),object=str(objects/Path(*label.split('.')).with_suffix('.olean')),required_constants=required,axioms=axioms((rp.parent/'stdout').read_text(),required),seconds=r['elapsed_seconds']);return value
 pending={x['module']:x for x in m['modules'] if x['kind']!='final'};running={};available=cpus[:a.jobs]
 try:
  with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
   while pending or running:
    for name,x in list(pending.items()):
     if not available:break
     if all(dep in results or dep not in names for dep in x['dependencies']):
      cpu=available.pop(0);running[pool.submit(compile_module,x,cpu,a.memory_gib)]=(name,cpu);del pending[name]
    need(bool(running),'acyclic complete dependencies');done,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
    for f in done:
     name,cpu=running.pop(f);results[name]=f.result();available.append(cpu)
    atomic(out/'PROGRESS.json',dict(status='ACTUALLY_COMPILING_FULL_SCALAR_CERTIFICATE',completed=len(results),total=len(m['modules']),rows=m['rows'],seconds=time.monotonic()-started))
  final=next(x for x in m['modules'] if x['kind']=='final');results[final['module']]=compile_module(final,cpus[0],192)
  audit_root=out/'independent-source';audit=audit_root/'RamanujanPV'/m['namespace'].split('.')[-1]/'ControllerAudit.lean';audit.parent.mkdir(parents=True);need(not audit.exists(),'fresh independent audit source');audit.write_text('import '+m['final_module']+'\nexample : RamanujanPV.FullFiniteScalars.ScalarCertificate 38358837683 '+str(m['stop'])+' '+m['namespace']+'.allRows := '+m['namespace']+'.all_scalars\n#print axioms '+m['namespace']+'.all_scalars\n');ar=dict(module=m['namespace']+'.ControllerAudit',source=str(audit),source_sha256=sha(audit),source_root=audit_root,standard_constants=[m['namespace']+'.all_scalars']);independent=compile_module(ar,cpus[0],192)
  records=[results[x['module']] for x in m['modules']]+[independent]
  result=dict(schema='RAMANUJAN_FULL_SCALAR_KERNEL_RESULT_V1',status='ALL_SCALAR_ENCLOSURE_AND_COVERAGE_KERNEL_CHECKS_PASS_COUNTS_OPEN_NOT_C_PV',manifest=str(a.manifest.resolve()),manifest_sha256=sha(a.manifest),rows=m['rows'],stop=m['stop'],full_locked_prefix=m['full_locked_prefix'],records=records,seconds=time.monotonic()-started,controller_sha256=sha(__file__),prime_counts_formally_proved_here=False,source_first_PV=False,combined_worker_limit_bytes=a.jobs*a.memory_gib*1024**3,final_independent_audit_limit_bytes=192*1024**3,host_memavailable_before_bytes=mem,host_reserve_bytes=512*1024**3)
  atomic(out/'RESULT.json',result);print(json.dumps(validate(out/'RESULT.json')))
 except Exception as error:
  atomic(out/'FAILED.json',dict(status='FAILED_ATTEMPT_PRESERVED_NO_SCALAR_ACCEPTANCE',reason=str(error),completed=len(results),seconds=time.monotonic()-started));raise
if __name__=='__main__':main()
