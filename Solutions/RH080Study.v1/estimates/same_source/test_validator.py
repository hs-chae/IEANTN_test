#!/usr/bin/env python3
"""Exercise actual replay CLI dependency/freshness guards under all Python modes."""
import argparse,copy,hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path

def need(c,m):
 if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--repository',type=Path,required=True);p.add_argument('--run',type=Path,required=True);a=p.parse_args();need(not a.run.exists(),'Fresh control directory required');a.run.mkdir(parents=True);script=Path(__file__).with_name('reproduce.py');original=json.loads(a.context.read_text());rows=[]
 for mode in [[],['-O'],['-OO']]:
  for name,guard in [('compiler_hash','Pinned compiler bytes differ'),('source_revision','Generic source pins differ'),('path_order','Generic package order/name differs'),('path_population','Generic path population differs'),('existing_run','Fresh run required')]:
   stem=str(len(mode) and mode[0][1:] or 'normal')+'-'+name;c=copy.deepcopy(original);run=a.run/(stem+'-replay')
   if name=='compiler_hash':c['compiler_sha256']='0'*64
   if name=='source_revision':c['generic_dependencies'][0]['revision']='0'*40
   if name=='path_order':
    x=c['generic_lean_path'].split(':');x[0],x[1]=x[1],x[0];c['generic_lean_path']=':'.join(x)
   if name=='path_population':c['generic_lean_path']=':'.join(c['generic_lean_path'].split(':')[:-1])
   if name=='existing_run':run.mkdir()
   context=a.run/(stem+'.json');context.write_text(json.dumps(c,indent=2)+'\n');cmd=[sys.executable,*mode,str(script),'--repository',str(a.repository),'--context',str(context),'--run',str(run)];r=subprocess.run(cmd,capture_output=True);out=a.run/(stem+'.stdout');err=a.run/(stem+'.stderr');out.write_bytes(r.stdout);err.write_bytes(r.stderr);need(r.returncode!=0 and guard in r.stderr.decode(),'Expected actual CLI guard did not reject '+stem);need(not (run/'RESULT.json').exists(),'Rejected run emitted acceptance');rows.append(dict(name=name,python_options=mode,command=cmd,returncode=r.returncode,required_guard=guard,context_sha256=sha(context),stdout_sha256=sha(out),stderr_sha256=sha(err)))
 result=dict(status='PASS_ACTUAL_CLI_REJECTION_CONTROLS_ALL_PYTHON_MODES',cases=rows,controller_sha256=sha(Path(__file__)),replay_controller_sha256=sha(script));fd,name=tempfile.mkstemp(dir=a.run,prefix='.acceptance-');q=Path(name)
 try:
  with os.fdopen(fd,'w') as f:json.dump(result,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
  os.link(q,a.run/'RESULT.json')
 finally:q.unlink()
 print(json.dumps(dict(status=result['status'],cases=len(rows))))
if __name__=='__main__':main()
