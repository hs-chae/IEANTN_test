#!/usr/bin/env python3
"""External exact-rational review; ordinary Python, explicitly NOT source-first PV."""
from pathlib import Path
import argparse,ast,hashlib,json,os,signal,subprocess,sys,time
D=Path('/data/ivy-rh-080-20261125');S=D/'network/Solutions/RH080Study.v1';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
class Guard(ast.NodeTransformer):
 def __init__(self,filename):self.filename=filename;self.count=0
 def visit_Assert(self,n):
  self.count+=1
  return ast.copy_location(ast.If(test=ast.UnaryOp(op=ast.Not(),operand=n.test),body=[ast.Raise(exc=ast.Call(func=ast.Name(id='RuntimeError',ctx=ast.Load()),args=[ast.Constant(value='EXACT_CHECK_FAILED:'+self.filename+':'+str(n.lineno))],keywords=[]),cause=None)],orelse=[]),n)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--trial',required=True);p.add_argument('--prefix',required=True);p.add_argument('--script',action='append',required=True);p.add_argument('--mode',choices=['normal','O','OO'],required=True);p.add_argument('--run',type=Path,required=True);a=p.parse_args();need(not a.run.exists(),'Fresh external replay required');x=json.loads((S/'ablation/followup/evidence/FOLLOWUP_REAUDIT_normal.json').read_text());t=next(t for t in x['trials'] if t['id']==a.trial);pr=next(p for p in t['timely_prefixes'] if Path(p['path']).name==a.prefix);P=Path(pr['path']);a.run.mkdir(parents=True);src=a.run/'guarded';src.mkdir();sources=[]
 for f in pr['files']:
  q=P/f['file'];need(H(q)==f['sha256'],'Locked input changed')
  if q.suffix!='.py':continue
  tree=ast.parse(q.read_text());g=Guard(q.name);out=ast.fix_missing_locations(g.visit(tree));need(not any(isinstance(n,ast.Assert) for n in ast.walk(out)),'Assertion guard left unconverted');dest=src/q.name;dest.write_text(ast.unparse(out)+'\n');sources.append(dict(original=str(q),original_sha256=H(q),guard_strengthened_sha256=H(dest),assert_statements_replaced=g.count))
 env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1';rows=[]
 for name in a.script:
  need((src/name).is_file(),'Unassigned numeric script');cmd=['/usr/bin/prlimit','--as='+str(64*2**30),'--','/usr/bin/time','-v',sys.executable]+([] if a.mode=='normal' else ['-'+a.mode])+[str(src/name)];start=time.monotonic()
  with (a.run/(name+'.stdout')).open('wb') as out,(a.run/(name+'.stderr')).open('wb') as err:
   proc=subprocess.Popen(cmd,env=env,cwd=src,stdout=out,stderr=err,start_new_session=True)
   try:code=proc.wait(timeout=900)
   except subprocess.TimeoutExpired:
    os.killpg(proc.pid,signal.SIGTERM)
    try:proc.wait(timeout=10)
    except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
    code=124
  rows.append(dict(script=name,returncode=code,seconds=time.monotonic()-start,command=cmd,stdout_sha256=H(a.run/(name+'.stdout')),stderr_sha256=H(a.run/(name+'.stderr'))))
  if code:break
 result=dict(status='PASS_EXTERNAL_EXACT_RATIONAL_GUARD_STRENGTHENED_REPLAY' if all(x['returncode']==0 for x in rows) and len(rows)==len(a.script) else 'FAIL_OR_RESOURCE_LIMIT_EXTERNAL_RATIONAL_REPLAY',trial=a.trial,prefix=a.prefix,mode=a.mode,sources=sources,commands=rows,source_first_PV=False,kernel_proof=False,original_inputs_changed=False,meaning='Ordinary exact-rational external evidence plus separately reviewed written analytic proof. Only assert guards were made explicit for optimization robustness; arithmetic AST/parameters retained. No formal Python semantics/source correspondence proof claimed.');(a.run/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','trial','mode']}))
if __name__=='__main__':main()
