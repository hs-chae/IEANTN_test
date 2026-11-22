#!/usr/bin/env python3
"""Resolve pinned generic dependencies in a clean checkout; no app cache allowed."""
from pathlib import Path
import argparse,json,hashlib,subprocess,os
S=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--packages',type=Path,required=True);p.add_argument('--compiler',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
def need(c,m):
 if not c:raise ValueError(m)
need(not a.out.exists(),'fresh context output');reference=S.parent/'scripts/GENERIC_CONTEXT.json';j=json.loads(reference.read_text());comp=a.compiler.resolve();need(hashlib.sha256(comp.read_bytes()).hexdigest()==j['compiler_sha256'],'compiler SHA256 differs from pinned version');libs=[]
for row in j['generic_dependencies']:
 q=(a.packages/row['name']).resolve();r=subprocess.run(['git','-C',str(q),'rev-parse','HEAD'],capture_output=True,text=True);need(r.returncode==0 and r.stdout.strip()==row['revision'],'dependency commit differs:'+row['name']);lib=q/'.lake/build/lib/lean';row.update(path=str(q),library=str(lib),library_present=lib.is_dir())
 if row['name']!='Cli':need(lib.is_dir(),'build generic dependency:'+row['name']);libs.append(str(lib))
j.update(compiler=str(comp),generic_libraries=libs,reference_context_sha256=hashlib.sha256(reference.read_bytes()).hexdigest(),new_application_object_root=None,purpose='Portable exact generic dependency map only; all application/checker sources replayed separately');a.out.parent.mkdir(parents=True,exist_ok=True);tmp=a.out.with_suffix('.pending');tmp.write_text(json.dumps(j,indent=2)+'\n');os.replace(tmp,a.out);print('PASS_PINNED_GENERIC_CONTEXT',a.out)
