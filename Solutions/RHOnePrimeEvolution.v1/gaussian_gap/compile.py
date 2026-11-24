#!/usr/bin/env python3
"""Sequential, one-compiler development replay with immutable source snapshots.
Final whole-closure replay is a separate parent acceptance gate.
"""
import argparse,hashlib,json,os,re,subprocess,time
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run',type=Path,required=True);p.add_argument('--module',action='append',required=True);p.add_argument('--bank',type=Path,action='append',default=[]);a=p.parse_args()
 here=Path(__file__).resolve().parent;study=here.parent;ctx=json.loads((study/'scripts/LOCAL_CONTEXT.json').read_text());D=a.run.resolve()
 if D.exists():raise SystemExit('Fresh run required')
 source,objects,logs=[D/n for n in ('source','objects','logs')]
 for d in (source,objects,logs):d.mkdir(parents=True)
 (D/'compile.executed.py').write_bytes(Path(__file__).read_bytes());env=os.environ.copy();env['LEAN_PATH']=':'.join([str(objects)]+[str(b.resolve(strict=True)) for b in a.bank]+[ctx['mathlib_lean_path']]);rows=[]
 for m in a.module:
  src=source/(m.replace('.','/')+'.lean');src.parent.mkdir(parents=True,exist_ok=True)
  original=study.parent.parent/(m.replace('.','/')+'.lean') if m.startswith('IEANTN.') else here/(m+'.lean')
  src.write_bytes(original.read_bytes())
 for m in a.module:
  available=int(re.search(r'MemAvailable:\s+(\d+)',Path('/proc/meminfo').read_text())[1])*1024
  if available<256*1024**3:raise SystemExit('Preserve host RAM reserve')
  src=source/(m.replace('.','/')+'.lean');out=objects/(m.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True);cmd=['/usr/bin/prlimit','--as=68719476736','--','/usr/bin/time','-v',ctx['compiler'],'--root='+str(source),'-j2','-o',str(out),str(src)];start=time.monotonic()
  with (logs/(m+'.stdout')).open('wb') as stdout,(logs/(m+'.stderr')).open('wb') as stderr:r=subprocess.run(cmd,env=env,stdout=stdout,stderr=stderr)
  row=dict(module=m,returncode=r.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),object_sha256=sha(out) if out.exists() else None,stdout_sha256=sha(logs/(m+'.stdout')),stderr_sha256=sha(logs/(m+'.stderr')),command=cmd);rows.append(row)
  if r.returncode:print((logs/(m+'.stdout')).read_text()[-6000:]);break
 result=dict(status='PASS_SCOPED_DEV_COMPILATION' if len(rows)==len(a.module) and all(q['returncode']==0 for q in rows) else 'FAILED',results=rows,lean_path=env['LEAN_PATH'],scope='Sequential development compile with explicitly supplied proof banks. No fresh transitive/source-first-PV claim.')
 tmp=D/'RESULT.json.tmp'
 with tmp.open('x') as f:json.dump(result,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
 os.replace(tmp,D/'RESULT.json');print(json.dumps(result))
 if result['status']=='FAILED':raise SystemExit(1)
if __name__=='__main__':main()
