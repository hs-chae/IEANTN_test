#!/usr/bin/env python3
"""Independent source read/compile receipt for the sibling finite analytic bridge.

This is a bounded three-module incremental review, not a whole graph replay.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,resource,subprocess,time
from reproduce import read,save,need,sha,audit,COMPILER_SHA
B=Path(__file__).resolve().parent;N=B.parents[2];A=B.parent/'analytic'
BASE=Path('/data/ivy-rh-continuation-20261122/integration/public-final-v2/base')
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
 out=a.out.resolve();need(not out.exists(),'fresh output');ctx=read(N/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')
 need(sha(ctx['compiler'])==COMPILER_SHA,'compiler pin');need(sha(BASE/'BUILD.json')=='6f72bc4d2ba7dd34a8410ec53c0f0072a8c6d4d47f0bebb2613d7a7cc0c518cf','base receipt pin')
 base=read(BASE/'BUILD.json');need(base['status']=='PASS'and len(base['modules'])==111,'base complete')
 for r in base['modules']:
  need(r['returncode']==0 and sha(r['command'][-1])==r['source_sha256']and sha(BASE/'objects'/(r['module'].replace('.','/')+'.olean'))==r['object_sha256'],'base source/object association')
 out.mkdir();(out/'source').mkdir();(out/'objects').mkdir();(out/'logs').mkdir();start=time.monotonic();rows=[]
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out/'objects'),str(BASE/'objects'),*ctx['generic_libraries']])
 for mod in ['OcticFourier','BPTZeroCount','AbsoluteStieltjes']:
  orig=A/(mod+'.lean');src=out/'source'/orig.name;src.write_bytes(orig.read_bytes());ns=re.search(r'^namespace (\S+)',src.read_text(),re.M).group(1)
  expected=[ns+'.'+n for n in re.findall(r'^#print axioms (\S+)',src.read_text(),re.M)];obj=out/'objects'/(mod+'.olean')
  cmd=[ctx['compiler'],'--root='+str(out/'source'),'-j8','-o',str(obj),str(src)];st=time.monotonic()
  run=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=out/'source',env=env,text=True,capture_output=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(80*1024**3,80*1024**3)))
  (out/'logs'/(mod+'.stdout')).write_text(run.stdout);(out/'logs'/(mod+'.stderr')).write_text(run.stderr)
  need(run.returncode==0,'independent compile failed:'+mod);need(sha(src)==sha(orig),'source changed during review')
  rows.append({'module':mod,'source_sha256':sha(src),'object_sha256':sha(obj),'command':cmd,'returncode':run.returncode,'seconds':time.monotonic()-st,'peak_RSS_KiB':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',run.stderr).group(1)),'axiom_audits':audit(run.stdout,expected)})
  print('PASS',mod,flush=True)
 save(out/'RESULT.json',{'status':'PASS_INDEPENDENT_THREE_SOURCE_RECOMPILATION','reviewer':'octic worker; distinct from analytic proof author','scope':'Incremental source/object-pinned111 bank; no complete analytic graph claim','controller_sha256':sha(__file__),'compiler_sha256':COMPILER_SHA,'seconds':time.monotonic()-start,'modules':rows,'source_first_PV':False})
if __name__=='__main__':main()
