#!/usr/bin/env python3
"""Exercise the actual portable rational-review CLI guards under all optimizations."""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path

def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',type=Path,required=True);a=ap.parse_args();need(not a.run.exists(),'Fresh CLI control directory required');a.run.mkdir(parents=True);here=Path(__file__).resolve().parent;runner=here/'replay_rational_checks.py';original=here.parent/'timely-prefixes/cube-L2_E2_D1_V1-r1/prefix-0002';rows=[]
 for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
  d=a.run/mode;d.mkdir();p=d/'prefix-0002';shutil.copytree(original,p);lock=(p/'LOCK.json').read_bytes();source=p/'scalar_checks.py';oldsource=source.read_bytes()
  def case(name,args,want):
   out=d/(name+'-run');cmd=[sys.executable]+flags+[str(runner),'--prefix-dir',str(p),'--trial','cube-L2_E2_D1_V1-r1','--prefix','prefix-0002','--script','scalar_checks.py','--mode',mode,'--run',str(out)]+args;r=subprocess.run(cmd,capture_output=True);(d/(name+'.stdout')).write_bytes(r.stdout);(d/(name+'.stderr')).write_bytes(r.stderr);text=r.stdout.decode()+r.stderr.decode();need(r.returncode!=0 and want in text,'Wrong rejection '+mode+'/'+name);need(not (out/'RESULT.json').exists(),'Rejected CLI published acceptance');rows.append(dict(mode=mode,name=name,returncode=r.returncode,expected=want,command=cmd,stdout_sha256=sha(d/(name+'.stdout')),stderr_sha256=sha(d/(name+'.stderr'))))
  case('unknown_option',['--bogus'],'unrecognized arguments');existing=d/'existing-run';existing.mkdir();case('existing_run',['--run',str(existing)],'Fresh external replay required')
  source.write_bytes(oldsource+b'\n');case('changed_source',[],'Locked input changed');source.write_bytes(oldsource)
  (p/'LOCK.json').write_text('{"files":[],"files":[]}');case('duplicate_json',[],'Duplicate JSON key');(p/'LOCK.json').write_bytes(lock)
  (p/'LOCK.json').write_text('{"files":NaN}');case('nonfinite_json',[],'Nonfinite JSON');(p/'LOCK.json').write_bytes(lock)
  j=json.loads(lock);j['files'][0]['path']='../outside.py';(p/'LOCK.json').write_text(json.dumps(j));case('unsafe_locked_filename',[],'Unsafe locked filename');(p/'LOCK.json').write_bytes(lock)
 result=dict(status='PASS_PORTABLE_RATIONAL_REVIEW_ACTUAL_CLI_GUARDS_NORMAL_O_OO',cases=rows,count=len(rows),controller_sha256=sha(Path(__file__)),replay_controller_sha256=sha(runner));fd,name=tempfile.mkstemp(dir=a.run,prefix='.receipt-');q=Path(name)
 try:
  with os.fdopen(fd,'w') as f:json.dump(result,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
  os.link(q,a.run/'RESULT.json')
 finally:q.unlink()
 print(json.dumps(dict(status=result['status'],cases=len(rows))))
if __name__=='__main__':main()
