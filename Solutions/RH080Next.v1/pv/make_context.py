#!/usr/bin/env python3
"""Construct a clean local proof context from exactly pinned dependency checkouts."""
import argparse,hashlib,json,os,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--compiler',type=Path,required=True);ap.add_argument('--mathlib',type=Path,required=True);ap.add_argument('--packages',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    d=json.loads((HERE/'DEPENDENCIES.json').read_text());compiler=a.compiler.resolve();need(compiler.is_file(),'Compiler missing');need(sha(compiler)==d['compiler_sha256'],'Compiler bytes differ from pinned toolchain')
    version=subprocess.check_output([str(compiler),'--version'],text=True).strip();need(version==d['compiler_version'],'Compiler version mismatch')
    roots=[]
    for row in d['generic_dependencies']:
        source=a.mathlib if row['name']=='mathlib'else (a.packages or a.mathlib/'.lake/packages')/row['name']
        need(source.is_dir(),'Dependency missing: '+str(source))
        rev=subprocess.check_output(['git','-C',str(source),'rev-parse','HEAD'],text=True).strip();need(rev==row['revision'],'Dependency revision differs: '+row['name'])
        obj=source/'.lake/build/lib/lean';need(obj.is_dir(),'Generic dependency objects not built: '+str(obj));roots.append(str(obj.resolve()))
    need(not a.output.exists(),'Fresh context output required');a.output.parent.mkdir(parents=True,exist_ok=True)
    result=dict(status='PINNED_GENERIC_CONTEXT_ONLY',compiler=str(compiler),compiler_sha256=sha(compiler),compiler_version=version,generic_lean_path=':'.join(roots),generic_dependencies=d['generic_dependencies'])
    with a.output.open('x')as f:json.dump(result,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
    print(json.dumps(dict(status=result['status'],dependencies=len(roots))))
if __name__=='__main__':main()
