#!/usr/bin/env python3
"""Locate clean same-pin generic libraries after root `lake exe cache get`."""
from pathlib import Path
import argparse,hashlib,json,subprocess
p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args();s=Path(__file__).resolve().parents[1];n=s.parents[1];old=json.loads((s/'BUILD_CONTEXT.json').read_text());lean=Path(subprocess.check_output(['elan','which','lean'],cwd=n,text=True).strip())
if hashlib.sha256(lean.read_bytes()).hexdigest()!=old['compiler_sha256']:raise ValueError('exact pinned Linux Lean executable required')
rows=[];libs=[]
for oldrow in old['generic_dependencies']:
 d=n/'.lake/packages'/oldrow['name'];lib=d/'.lake/build/lib/lean';row=dict(oldrow,path=str(d),library=str(lib),library_present=lib.is_dir())
 if not oldrow['library_present'] and not lib.is_dir():rows.append(row);continue
 if not lib.is_dir() or subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip()!=oldrow['revision']:raise ValueError('missing/wrong generic pin '+oldrow['name'])
 if subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=d,text=True):raise ValueError('modified generic dependency')
 rows.append(row);libs.append(str(lib))
if a.out.exists():raise ValueError('fresh output context required')
a.out.write_text(json.dumps(dict(old,compiler=str(lean),generic_dependencies=rows,generic_libraries=libs),indent=2)+'\n');print(a.out)
