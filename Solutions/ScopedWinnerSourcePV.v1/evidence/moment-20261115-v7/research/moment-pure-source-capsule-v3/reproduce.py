"""Regenerate numerical data and build all565 pure moment/PNT sources from emptybank."""
from pathlib import Path
import argparse,hashlib,json,math,os,subprocess,sys,time
B=Path(__file__).resolve().parent
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse(text):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicateJSON '+k);d[k]=v
  return d
 def bad(x):raise ValueError('nonfiniteJSON '+x)
 def floating(x):
  y=float(x);need(math.isfinite(y),'overflowJSON');return y
 return json.loads(text,object_pairs_hook=pairs,parse_float=floating,parse_constant=bad)
def strict(p):return parse(p.read_text())
def atomic(p,d):
 q=p.with_suffix('.pending');q.write_text(json.dumps(d,indent=2)+'\n');os.replace(q,p)
def inputs():
 lock=strict(B/'REPRODUCER_LOCK.json')
 for r in lock['files']:
  p=B/r['path'];need(p.is_file()and not p.is_symlink()and p.stat().st_size==r['bytes']and sha(p)==r['sha256'],'reproducer input '+r['path'])
 graph=strict(B/'SOURCE_LOCK.json');need(len(graph['sources'])==565 and len(graph['roots'])==1124,'exact565sources1124roots');need(not list(B.rglob('*.olean'))and not list(B.rglob('*.pyc')),'no appobjects or Pythoncache inputs')
 for row in graph['sources']:
  p=B/row['path'];need(p.is_file()and not p.is_symlink()and sha(p)==row['sha256'],'exact graph source '+row['module'])
 return graph

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--environment',type=Path);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--jobs',type=int,default=8);ap.add_argument('--check-inputs-only',action='store_true');a=ap.parse_args();graph=inputs();need(1<=a.jobs<=12,'jobs1..12');out=a.out.resolve();need(not out.exists()and B not in out.parents,'fresh output outside immutable capsule');out.mkdir(parents=True);flags=[]if sys.flags.optimize==0 else['-O'if sys.flags.optimize==1 else'-OO'];records=[];start=time.monotonic();logs=out/'logs';logs.mkdir()
 def execute(name,cmd):
  t=time.monotonic();so=logs/(name+'.stdout');se=logs/(name+'.stderr');tm=logs/(name+'.time')
  with so.open('wb')as f,se.open('wb')as g:q=subprocess.run(['/usr/bin/time','-v','-o',str(tm),*cmd],stdout=f,stderr=g,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
  row=dict(name=name,command=cmd,exit_code=q.returncode,seconds=time.monotonic()-t,stdout_sha256=sha(so),stderr_sha256=sha(se),time_sha256=sha(tm));records.append(row);need(q.returncode==0,'route '+name);return row
 try:
  if a.check_inputs_only:
   for name,script in [('numerical-source','reproduce_numerics.py'),('graph-source','reproduce_kernel_graph.py')]:execute(name,[sys.executable,'-B',*flags,str(B/script),'--out',str(out/name),'--check-inputs-only'])
   atomic(out/'RECEIPT.json',dict(status='PASS565_AND_BOTH_CHILD_SOURCE_IDENTITY_ROUTES_ONLY_NOT_PROOF',source_modules=565,python_optimization=sys.flags.optimize,records=records,application_object_inputs=[]));return
  need(a.environment is not None and a.environment.is_file(),'public generic environment required');env=strict(a.environment);compiler=Path(env['compiler']);need(sha(compiler)==graph['compiler_sha256'],'pinned kernel');clang=compiler.with_name('clang')
  execute('numerical-regeneration',[sys.executable,'-B',*flags,str(B/'reproduce_numerics.py'),'--compiler',str(clang),'--out',str(out/'numerics')]);numeric=strict(out/'numerics/RECEIPT.json');need(numeric['status']=='PASS_ALL_DETERMINISTIC_C_PROPOSALS_REGENERATED_AND_SOURCE_WORD_DATA_MATCHED','full actual regenerated numerical data')
  execute('full-source-graph',[sys.executable,'-B',*flags,str(B/'reproduce_kernel_graph.py'),'--environment',str(a.environment.resolve()),'--out',str(out/'proof'),'--jobs',str(a.jobs)]);proof=strict(out/'proof/RECEIPT.json');need(proof['status']=='PASS_PURE_MOMENT_PNT_SOURCE_COLD_EMPTY_BANK'and proof['source_modules']==565 and proof['theorem_roots']==1124 and proof['application_object_inputs']==[],'complete emptybank source/kernel consumer graph')
  need(len(proof['audits'])==1124 and all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'}for r in proof['audits']),'all typed complete final/new numeric roots standard')
  inputs();cleanup=[]
  # Delete only known regenerated numerical artifacts after data AND proofs pass.
  root=out/'numerics'
  for kind in ['height','mass','first_moment']:
   d=root/kind
   for name in ['program','run.stdout','prefix-proposal','prefix-run.stdout','prefix-proposal.cpp']:
    p=d/name
    if p.exists():
     need(p.is_file()and not p.is_symlink()and p.resolve().is_relative_to(root.resolve()),'exact owned regenerable cleanup');cleanup.append(dict(path=str(p.relative_to(out)),bytes=p.stat().st_size,sha256=sha(p)));p.unlink()
  atomic(out/'CLEANUP.json',dict(status='PASS_ONLY_EXACT_EXPERIMENT_OWNED_REGENERABLE_NUMERICAL_FILES_REMOVED',removed=cleanup,accepted_proof_objects_retained=True,original_sources_and_locked_inputs_unchanged=True,reproducer='reproduce.py regenerates identical proposals and verifies every source table before proof replay'))
  atomic(out/'RECEIPT.json',dict(status='PASS565_FRESH_PURE_MOMENT_NUMERICS_AND_FULL_ANT_SOURCE_GRAPH',seconds=time.monotonic()-start,source_modules=565,typed_standard_roots=1124,records=records,numerical_receipt_sha256=sha(out/'numerics/RECEIPT.json'),proof_receipt_sha256=sha(out/'proof/RECEIPT.json'),cleanup_receipt_sha256=sha(out/'CLEANUP.json'),source_lock_sha256=sha(B/'SOURCE_LOCK.json'),reproducer_sha256=sha(Path(__file__)),reproducer_lock_sha256=sha(B/'REPRODUCER_LOCK.json'),application_object_inputs=[],C_execution_proof_modules=False,source_first_PV=False,namespace_isolated=False,qualification='Pure kernel-only matching N+ verification of the new exactmoments andsame14-inputPNT conclusions. No Cexecutionproof imports/native axioms. Native C proposals are regenerated but untrusted and independently checked. This does not claim globalbest/optimality, a format effect, or PVnecessity. Namespace/resource receipts are separate.'))
 except Exception as ex:atomic(out/'FAILURE.json',dict(status='FAILED_PRESERVED_NO_COMPLETE_ACCEPTANCE',error=str(ex),records=records,seconds=time.monotonic()-start));raise
if __name__=='__main__':main()
