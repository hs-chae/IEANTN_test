#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: OpenAI (Codex)
"""Reproduce partial checkpoints; never claims full source-first PV."""
import argparse,hashlib,json,os,re,struct,subprocess,time
from fractions import Fraction
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read_json(p):
 def reject(s):raise ValueError('nonfinite JSON '+s)
 return json.loads(p.read_text(),parse_constant=reject)
def validate():
 rows=read_json(ROOT/'HASHES.json')['files'];names=[]
 for row in rows:
  n=row['path'];p=ROOT/n
  need(isinstance(n,str)and n and not Path(n).is_absolute()and '..'not in Path(n).parts,'unsafe manifest path')
  need(not p.is_symlink()and p.is_file()and p.resolve().is_relative_to(ROOT),'manifest source absent/aliased')
  need(sha(p)==row['sha256'],'source hash mismatch '+n);names.append(n)
 need(len(names)==len(set(names)),'duplicate manifest paths')
 return len(rows)
def run(cmd,out,role):
 start=time.monotonic()
 with(out/(role+'.stdout')).open('wb')as so,(out/(role+'.stderr')).open('wb')as se:
  p=subprocess.run(cmd,cwd=ROOT,stdout=so,stderr=se)
 d={'role':role,'command':list(map(str,cmd)),'exit_code':p.returncode,'seconds':time.monotonic()-start,'stdout_sha256':sha(out/(role+'.stdout')),'stderr_sha256':sha(out/(role+'.stderr'))}
 need(p.returncode==0,'command failed; inspect '+str(out/(role+'.stderr')))
 return d

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check-local',action='store_true');ap.add_argument('--run-numerics',action='store_true');ap.add_argument('--build-lean',action='store_true');ap.add_argument('--lean-prefix',type=Path);ap.add_argument('--out',type=Path);a=ap.parse_args()
 n=validate();need(a.check_local or a.run_numerics or a.build_lean,'choose at least one operation')
 if not(a.run_numerics or a.build_lean):print(json.dumps({'status':'LOCAL_SOURCE_HASHES_PASS','files':n,'full_source_PV':False}));return
 need(a.out is not None,'fresh --out required');out=a.out.resolve();need(not out.exists()and not out.is_relative_to(ROOT),'fresh output outside source checkout required');out.mkdir(parents=True)
 steps=[];details={}
 try:
  if a.run_numerics:
   need(a.lean_prefix is not None,'--lean-prefix required');t=a.lean_prefix.resolve();old=read_json(ROOT/'evidence/source-bundle-cpp-v1.json');pins=old['pins']
   for suffix in ['bin/clang','include/lean/lean.h','include/lean/config.h','lib/lean/libleanshared.so']:
    expected=[v for k,v in pins.items()if k.endswith('/'+suffix)];need(len(expected)==1,'ambiguous runtime pin '+suffix);need(sha(t/suffix)==expected[0],'wrong pinned runtime/compiler '+suffix)
   compiler=str(t/'bin/clang');includes=['-isystem','/usr/include/c++/11','-isystem','/usr/include/x86_64-linux-gnu/c++/11','-isystem','/usr/lib/gcc/x86_64-linux-gnu/11/include']
   binary=out/'scoped_all';steps.append(run([compiler,'-std=c++17','-O2','-I'+str(t/'include'),*includes,str(ROOT/'source/scoped_all_bundle.cpp'),'-L'+str(t/'lib/lean'),'-lleanshared','-Wl,-rpath,'+str(t/'lib/lean'),'-o',str(binary)],out,'build-scoped'))
   steps.append(run([str(binary)],out,'run-scoped'))
   records=read_json(ROOT/'evidence/ALL50_INPUT_SERIALIZATION_V1.json')['records'];lines=(out/'run-scoped.stdout').read_text().splitlines();need(len(records)==52 and len(lines)==52,'exact52 rows required');checks=[]
   for line,record in zip(lines,records):
    fields=line.split(',');need(len(fields)==5 and all(re.fullmatch(r'-?[0-9]+',x)for x in fields),'invalid exact integer output')
    lo,le,hi,he,ok=map(int,fields);need(le==-100 and he==-100 and ok==1 and lo<=hi,'invalid interval/flag');bound=Fraction(*map(int,record['bound']));direction=record['direction'];need(direction in ['upper','lower'],'invalid direction')
    need(Fraction(hi,2**100)<=bound if direction=='upper'else bound<=Fraction(lo,2**100),'frozen row bound failed');checks.append({'fact':record['native_fact'],'row':record['row_index'],'lo':str(lo),'hi':str(hi)})
   details['scoped_rows']=checks
   binary=out/'basis';steps.append(run([compiler,'-std=c++17','-O2',*includes,str(ROOT/'c/basis_fp128.cpp'),'-o',str(binary)],out,'build-basis'));steps.append(run([str(binary)],out,'run-basis'))
   raw=(out/'run-basis.stdout').read_bytes();need(len(raw)==144,'basis output bytes');words=struct.unpack('<18Q',raw);vals=[]
   for i,bound in enumerate([Fraction(1865,1000),Fraction(6365,10000),Fraction(516,1000)]):
    j=6*i;lo=sum(words[j+k]<<(64*k)for k in range(3));hi=sum(words[j+3+k]<<(64*k)for k in range(3));need(lo<=hi and Fraction(hi,2**128)<=bound,'basis quadrature upper cap failed');vals.append({'lower_word':str(lo),'upper_word':str(hi),'scale_power':128,'qualification':'Raw directed quadrature computation; not a verified integral theorem.'})
   details['basis_quadratures']=vals
  if a.build_lean:
   steps.append(run(['lake','update'],out,'lake-update'));steps.append(run(['lake','exe','cache','get'],out,'lake-cache'));steps.append(run(['lake','build','ScopedCheckpoint'],out,'lake-build'))
  validate();receipt={'status':'PARTIAL_CHECKPOINT_REPRODUCTION_PASS','full_source_PV':False,'steps':steps,'details':details,'warning':'Raw numerical execution and partial Lean modules do not complete the application-body or final theorem migration.'}
 except Exception as e:
  (out/'FAILURE.json').write_text(json.dumps({'status':'FAILED','error':str(e),'steps':steps},indent=2)+'\n');raise
 (out/'RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'status':receipt['status'],'full_source_PV':False}))
if __name__=='__main__':main()
