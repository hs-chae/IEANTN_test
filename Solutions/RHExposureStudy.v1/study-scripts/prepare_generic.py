#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,tarfile,io,os,time
W=Path('/ryu/hyunsik/playground/independence/codex/ivy');R=W/'ieantn-rh-propagation-20261120';D=Path('/data/ivy-rh-propagation-20261120')
ctx=json.loads((W/'ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1/BUILD_CONTEXT.json').read_text())
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(8*1024**2),b''):h.update(b)
 return h.hexdigest()
def tree(root,out):
 rows=[]
 for base,dirs,files in os.walk(root):
  dirs[:]=sorted(ds for ds in dirs if ds!='.git')
  for name in sorted(files):
   p=Path(base,name);rel=p.relative_to(root).as_posix()
   if p.is_symlink():
    if not p.resolve().is_relative_to(root.resolve()):raise RuntimeError('external symlink '+str(p))
    rows.append({'path':rel,'symlink':os.readlink(p)});continue
   rows.append({'path':rel,'bytes':p.stat().st_size,'sha256':sha(p)})
 out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps({'schema':'RH_TREE_V1','root':str(root),'files':rows},indent=2)+'\n')
 print(json.dumps({'tree':str(root),'files':len(rows),'bytes':sum(r.get('bytes',0)for r in rows),'manifest':str(out),'sha256':sha(out)}),flush=True)
 return {'path':str(out),'sha256':sha(out)}
mounts=[];lean=[];start=time.time()
toolchain=Path(ctx['compiler']).parent.parent
mounts.append({'source':str(toolchain),'target':'/opt/lean','role':'toolchain','manifest':tree(toolchain,R/'protocol/trees/toolchain.json')})
for dep in ctx['generic_dependencies']:
 name=dep['name'];src=D/'generic-source'/name
 if not src.exists():
  src.mkdir(parents=True)
  archive=subprocess.check_output(['git','-C',dep['path'],'archive',dep['revision']])
  with tarfile.open(fileobj=io.BytesIO(archive))as t:
   for m in t.getmembers():
    if m.name.startswith('/')or'..'in Path(m.name).parts:raise RuntimeError('unsafe generic archive path')
   t.extractall(src,filter='data')
 mounts.append({'source':str(src),'target':'/generic-source/'+name,'role':'generic','revision':dep['revision'],'manifest':tree(src,R/'protocol/trees'/('source-'+name+'.json'))})
 lib=Path(dep['library'])
 if lib.is_dir():
  target='/generic-lib/'+name;lean.append(target)
  mounts.append({'source':str(lib),'target':target,'role':'generic','revision':dep['revision'],'manifest':tree(lib,R/'protocol/trees'/('lib-'+name+'.json'))})
(R/'protocol/GENERIC_RUNTIME.json').write_text(json.dumps({'mounts':mounts,'lean_path':lean,'context':ctx,'elapsed_seconds':time.time()-start},indent=2)+'\n')
