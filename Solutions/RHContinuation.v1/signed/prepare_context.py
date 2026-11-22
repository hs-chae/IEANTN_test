#!/usr/bin/env python3
"""Map the exact pinned generic Lean source dependencies to a clean checkout.
No dependency versions or scientific sources are changed; no packages are installed."""
from pathlib import Path
import argparse,json,subprocess,hashlib
B=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--core',type=Path,required=True);p.add_argument('--compiler',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
if a.out.exists():raise ValueError('fresh context output required')
c=json.loads((B/'BUILD_CONTEXT.json').read_text());core=a.core.resolve();compiler=a.compiler.resolve()
if hashlib.sha256(compiler.read_bytes()).hexdigest()!=c['compiler_sha256']:raise ValueError('exact compiler hash differs')
c['compiler']=str(compiler);newlibs=[]
for d in c['generic_dependencies']:
 old=d['library'];root=core/'.lake/packages'/Path(d['path']).name
 if not root.is_dir():raise ValueError('missing pinned package; restore core lake-manifest dependencies first: '+str(root))
 rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
 if rev!=d['revision']:raise ValueError('pinned generic revision differs: '+d['name'])
 if subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True).strip():raise ValueError('tracked generic source is dirty: '+d['name'])
 d['path']=str(root);d['library']=str(root/'.lake/build/lib/lean')
 if old in c['generic_libraries']:
  if not Path(d['library']).is_dir():raise ValueError('generic library cache absent: '+d['name'])
  newlibs.append(d['library'])
c['generic_libraries']=newlibs;c['reproduction_core_revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=core,text=True).strip()
a.out.parent.mkdir(parents=True,exist_ok=True);tmp=a.out.with_suffix('.tmp');tmp.write_text(json.dumps(c,indent=2)+'\n');tmp.replace(a.out)
print('Pinned context mapped; exact source/compiler identities unchanged')
