#!/usr/bin/env python3
"""Actual fresh CLI rejection controls in normal/-O/-OO; explicit errors only."""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path

def need(ok,message):
 if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--run',type=Path,required=True);a=p.parse_args();need(not a.run.exists(),'Fresh controls directory required');a.run.mkdir(parents=True);S=Path(__file__).resolve().parent;R=S.parents[3];runner=S/'reproduce.py';base=json.loads(a.context.read_text());manifest=json.loads((S/'INPUT_MANIFEST.json').read_text());rows=[]
 for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
  dest=a.run/mode;dest.mkdir();repo=dest/'fixture';study=repo/'Solutions/RH080Study.v1/estimates/early369';study.mkdir(parents=True)
  for r in manifest['modules']:
   q=repo/r['path'];q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(R/r['path'],q)
  mp=study/'INPUT_MANIFEST.json';mp.write_text(json.dumps(manifest));original=mp.read_bytes();commands=[]
  def test(name,args,expected):
   output=dest/(name+'-output');cmd=[sys.executable]+flags+[str(runner),'--context',str(a.context),'--run',str(output)]+args
   run=subprocess.run(cmd,capture_output=True);(dest/(name+'.stdout')).write_bytes(run.stdout);(dest/(name+'.stderr')).write_bytes(run.stderr);text=run.stdout.decode()+run.stderr.decode();need(run.returncode!=0 and expected in text,'Wrong CLI rejection '+mode+'/'+name);need(not (output/'RESULT.json').exists(),'Rejected CLI published acceptance');commands.append(dict(name=name,command=cmd,returncode=run.returncode,expected=expected,stdout_sha256=sha(dest/(name+'.stdout')),stderr_sha256=sha(dest/(name+'.stderr'))))
  test('unknown_option',['--bogus'],'unrecognized arguments');test('wrong_lane',['--lane','other'],'invalid choice')
  existing=dest/'existing_output';existing.mkdir();test('existing_output',['--run',str(existing)],'Fresh run required')
  for name,change,expected in [('wrong_compiler_hash',lambda d:d.update(compiler_sha256='0'*64),'Pinned compiler bytes differ'),('wrong_generic_revision',lambda d:d['generic_dependencies'][0].update(revision='0'*40),'Generic source pins differ')]:
   d=json.loads(json.dumps(base));change(d);q=dest/(name+'.json');q.write_text(json.dumps(d));test(name,['--context',str(q)],expected)
  for name,text,expected in [('duplicate_context','{"compiler":1,"compiler":2}','Duplicate JSON key'),('nonfinite_context','{"compiler":NaN}','Nonfinite JSON')]:
   q=dest/(name+'.json');q.write_text(text);test(name,['--context',str(q)],expected)
  test('clean_missing_source',['--repository',str(repo/'missing')],'No such file or directory')
  first=repo/manifest['modules'][0]['path'];old=first.read_bytes();first.write_bytes(old+b'\n');test('changed_source',['--repository',str(repo)],'Source provider hash changed');first.write_bytes(old)
  for name,change,expected in [('unsafe_path',lambda d:d['modules'][0].update(path='../escape.lean'),'Unsafe provider path'),('duplicate_module',lambda d:d['modules'].insert(1,d['modules'][0]),'Duplicate module identity'),('missing_dependency',lambda d:d['modules'].reverse(),'Non-generic dependency absent')]:
   d=json.loads(original);change(d);mp.write_text(json.dumps(d));test(name,['--repository',str(repo)],expected);mp.write_bytes(original)
  mp.write_text('{"modules":[],"modules":[]}');test('duplicate_manifest',['--repository',str(repo)],'Duplicate JSON key');mp.write_bytes(original)
  rows.append(dict(mode=mode,commands=commands))
 result=dict(status='PASS_ACTUAL_CLI_GUARDS_ALL_THREE_OPTIMIZATION_MODES',cases=sum(len(r['commands']) for r in rows),modes=rows,controller_sha256=sha(Path(__file__)),tested_runner_sha256=sha(runner));fd,name=tempfile.mkstemp(dir=a.run,prefix='.acceptance-');q=Path(name)
 try:
  with os.fdopen(fd,'w') as f:json.dump(result,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
  os.link(q,a.run/'RESULT.json')
 finally:q.unlink()
 print(json.dumps(dict(status=result['status'],cases=result['cases'])))
if __name__=='__main__':main()
