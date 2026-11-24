#!/usr/bin/env python3
"""Copy exact pinned packages into owned scratch before genuine native-link builds.
Original generic source/object caches are then reused only as copy inputs.
"""
import argparse,hashlib,json,shutil,subprocess,time
from pathlib import Path

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--repository',type=Path,required=True);p.add_argument('--destination',type=Path,required=True);a=p.parse_args()
 R=a.repository.resolve(strict=True);D=a.destination.resolve()
 if D.exists():raise SystemExit('Fresh private package copy directory required')
 D.mkdir();C=json.loads((R/'Solutions/RHOnePrimeEvolution.v1/scripts/LOCAL_CONTEXT.json').read_text());rows=[];start=time.monotonic()
 for item in C['generic_dependency_versions']:
  src=Path(item['path']).resolve(strict=True);dst=D/item['name']
  revision=subprocess.check_output(['git','-C',str(src),'rev-parse','HEAD'],text=True).strip()
  clean=subprocess.check_output(['git','-C',str(src),'status','--porcelain','--untracked-files=no'],text=True)
  if revision!=item['revision'] or clean:raise SystemExit('Original pin/source mismatch '+item['name'])
  shutil.copytree(src,dst,symlinks=True)
  copied_revision=subprocess.check_output(['git','-C',str(dst),'rev-parse','HEAD'],text=True).strip()
  copied_clean=subprocess.check_output(['git','-C',str(dst),'status','--porcelain','--untracked-files=no'],text=True)
  if copied_revision!=revision or copied_clean:raise SystemExit('Private copied source mismatch '+item['name'])
  link=R/'.lake/packages'/item['name']
  if not link.is_symlink():raise SystemExit('Expected solely our package symlink '+str(link))
  link.unlink();link.symlink_to(dst,target_is_directory=True)
  rows.append(dict(name=item['name'],revision=revision,original=str(src),isolated=str(dst),copied_tracked_source_clean=True))
  print(json.dumps(rows[-1]),flush=True)
 (D/'COPY_RECEIPT.json').write_text(json.dumps(dict(status='PASS_PINNED_PRIVATE_GENERIC_PACKAGE_COPIES',seconds=time.monotonic()-start,packages=rows,controller_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),indent=2)+'\n')
if __name__=='__main__':main()
