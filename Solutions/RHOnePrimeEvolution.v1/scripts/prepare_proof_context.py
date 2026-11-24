#!/usr/bin/env python3
"""Record portable proof arguments from freshly installed pinned generic libraries."""
import argparse,hashlib,json,os,subprocess
from pathlib import Path

def main():
 p=argparse.ArgumentParser(description=__doc__,allow_abbrev=False);p.add_argument('--packages',type=Path,required=True);p.add_argument('--compiler',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 S=Path(__file__).resolve().parents[1];spec=json.loads((S/'portable/SOURCE_MANIFEST.json').read_text());compiler=a.compiler.resolve(strict=True);out=a.output.resolve()
 if out.exists():raise ValueError('Fresh context destination required')
 version=subprocess.check_output([str(compiler),'--version'],text=True).strip()
 if 'version 4.34.0-rc2' not in version:raise ValueError('Pinned Lean4.34.0-rc2 required')
 libraries=[];rows=[]
 for dep in spec['generic_dependencies']:
  package=(a.packages/dep['name']).resolve(strict=True);library=package/'.lake/build/lib/lean'
  if '/.lake/packages/' not in str(library):raise ValueError('Use the documented .lake/packages layout required by the frozen generic-path guard')
  if not library.is_dir():raise ValueError('Pinned generic cache missing: '+dep['name'])
  head=subprocess.check_output(['git','-C',str(package),'rev-parse','HEAD'],text=True).strip();dirty=subprocess.check_output(['git','-C',str(package),'status','--porcelain','--untracked-files=no'],text=True)
  if head!=dep['revision'] or dirty:raise ValueError('Generic source pin/cleanliness mismatch '+dep['name'])
  libraries.append(str(library));rows.append({'name':dep['name'],'revision':head})
 data={'status':'PINNED_GENERIC_ARGUMENTS_ONLY_NOT_MATHEMATICAL_PROOF','compiler':str(compiler),'compiler_sha256':hashlib.sha256(compiler.read_bytes()).hexdigest(),'compiler_version':version,'generic_lean_path':':'.join(libraries),'generic_dependencies':rows}
 out.parent.mkdir(parents=True,exist_ok=True);tmp=out.with_name(out.name+'.new')
 with tmp.open('x') as f:json.dump(data,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
 os.replace(tmp,out);print(json.dumps(data))
if __name__=='__main__':
 try:main()
 except (ValueError,OSError,subprocess.CalledProcessError) as e:raise SystemExit(str(e))
