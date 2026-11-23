#!/usr/bin/env python3
"""Fetch clean exact generic source revisions into a fresh owned directory.

--check only validates an existing directory and performs no network or writes.
"""
from pathlib import Path
import argparse,json,re,subprocess,sys
sys.dont_write_bytecode=True
from prepare_bundle import need,strict,save,sha,verify

def main():
 here=Path(__file__).resolve().parent;p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--check',action='store_true');p.add_argument('--pins',type=Path);p.add_argument('--reference',type=Path);a=p.parse_args()
 need((a.pins is None)==(a.reference is None),'provide both explicit development metadata paths or neither')
 if a.pins is None:verify(here)
 pins=a.pins or here/'GENERIC_DEPENDENCY_PINS.json';ref=a.reference or here/'network/Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json';d=strict(pins);ctx=strict(ref);rows={r['name']:r for r in d['packages']};need(len(rows)==len(d['packages'])==9,'exact nine packages')
 for dep in ctx['generic_dependencies']:
  r=rows[dep['name']];need(r['rev']==dep['revision']and re.fullmatch('[0-9a-f]{40}',r['rev'])and r['url'].startswith('https://github.com/'),'exact package source pin')
 out=a.out.resolve();need(a.check or not out.exists(),'fresh source directory required')
 if not a.check:out.mkdir(parents=True)
 accepted=[]
 for dep in ctx['generic_dependencies']:
  r=rows[dep['name']];target=out/dep['name']
  if not a.check:
   target.mkdir();subprocess.run(['git','init','--quiet',str(target)],check=True);subprocess.run(['git','remote','add','origin',r['url']],cwd=target,check=True);subprocess.run(['git','fetch','--quiet','--depth','1','origin',r['rev']],cwd=target,check=True);subprocess.run(['git','checkout','--quiet','--detach','FETCH_HEAD'],cwd=target,check=True)
  need(target.is_dir()and not target.is_symlink(),'package source absent/linked');head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=target,text=True).strip();need(head==r['rev'],'package revision differs')
  need(subprocess.run(['git','diff','--quiet','HEAD','--'],cwd=target).returncode==0,'modified package source');accepted.append({'name':dep['name'],'url':r['url'],'revision':head})
 if not a.check:save(out/'FETCH_RECEIPT.json',{'status':'PASS_EXACT_NINE_GENERIC_SOURCE_CHECKOUTS','pins_sha256':sha(pins),'reference_sha256':sha(ref),'packages':accepted})
 print('PASS_EXACT_NINE_GENERIC_SOURCE_CHECKOUTS_READ_ONLY_CHECK'if a.check else'PASS_EXACT_NINE_GENERIC_SOURCE_CHECKOUTS')
if __name__=='__main__':main()
