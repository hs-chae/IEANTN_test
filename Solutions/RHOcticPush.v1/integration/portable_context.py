#!/usr/bin/env python3
"""Write a relocated generic-only context without changing any version pin."""
from pathlib import Path
import argparse,hashlib,json,subprocess
R=Path(__file__).resolve().parents[3]
def need(x,msg):
 if not x:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--packages',type=Path,default=R/'.lake/packages');p.add_argument('--compiler',type=Path);a=p.parse_args();need(not a.out.exists(),'fresh context file required');ref=json.loads((R/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json').read_text());compiler=a.compiler.resolve()if a.compiler else Path(subprocess.check_output(['elan','which','lean'],cwd=R,text=True).strip()).resolve();need(sha(compiler)==ref['compiler_sha256'],'pinned compiler binary differs');deps=[]
 for old in ref['generic_dependencies']:
  root=(a.packages/old['name']).resolve();need(root.is_dir(),'missing package:'+old['name']);need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==old['revision'],'wrong dependency revision:'+old['name']);need(subprocess.run(['git','diff','--quiet','HEAD','--'],cwd=root).returncode==0,'tracked dependency source changed:'+old['name']);lib=root/'.lake/build/lib/lean';need(not old['library_present']or lib.is_dir(),'generic cache missing:'+old['name']);deps.append({**old,'path':str(root),'library':str(lib),'library_present':old['library_present'],'tracked_source_clean':True})
 out={**ref,'compiler':str(compiler),'generic_dependencies':deps,'generic_libraries':[d['library']for d in deps if d['library_present']]};a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(out,indent=2)+'\n');print('PASS_RELOCATED_IDENTICAL_GENERIC_SOURCE_AND_COMPILER_PINS')
if __name__=='__main__':main()
