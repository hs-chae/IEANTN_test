#!/usr/bin/env python3
"""Supplementary exact-runtime import compatibility checks; no discovery."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import subprocess

MODULES=['IEANTN.Vocabulary.ZeroFreeHalfPlane','IEANTN.Nodes.FKS2.v2.Conclusions','RamanujanPV.CoupledLargeMargin','RamanujanPV.PrimeBaseCombinedResult']
HELPER=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-exposure-maximal-20261109/sources/ieantn-protected-workspace-20260925-NrAB5O/app/IEANTN/web/server/agent-sandbox.py')

def need(ok,msg):
    if not ok:raise ValueError(msg)

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--spec',type=Path,required=True);p.add_argument('--out',type=Path,required=True);args=p.parse_args()
    args.out=args.out.resolve();need(not args.out.exists()and args.out.is_relative_to('/data/ivy-rh-propagation-20261120/setup'),'fresh owned output required')
    original=json.loads(args.spec.read_bytes());need(original.get('network')=='offline','offline exact-runtime spec required')
    need(sha(HELPER)=='79c1428403befb974bf4daeada0c130addd60ff952cef4b62ca74ef18ae6d79d','namespace helper differs')
    args.out.mkdir(parents=True);(args.out/'root').mkdir()
    program='''from pathlib import Path
import json,subprocess
Path('/work/objects').mkdir(exist_ok=True)
results=[]
for i,name in enumerate(MODULES):
    path=Path('/work/Import'+str(i)+'.lean')
    path.write_text('import '+name+'\\nexample : True := by trivial\\n')
    command=['/opt/lean/bin/lean','-j8','-o','/work/objects/Import'+str(i)+'.olean',str(path)]
    p=subprocess.run(command,capture_output=True,text=True,timeout=300)
    results.append({'module':name,'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'olean_created':Path('/work/objects/Import'+str(i)+'.olean').is_file()})
print(json.dumps({'checks':results,'status':'PASS_NATIVE_CACHE_IMPORT_COMPATIBILITY'if all(r['returncode']==0 and r['olean_created']for r in results)else'FAIL_NATIVE_CACHE_IMPORT_COMPATIBILITY'}))
'''.replace('MODULES',repr(MODULES))
    spec=dict(original);spec.update(root=str(args.out/'root'),cwd='/work',command=['/usr/bin/python3.10','-I','-B','-c',program])
    path=args.out/'OS_SPEC.json';path.write_text(json.dumps(spec,indent=2)+'\n')
    command=['unshare','--user','--map-root-user','--mount','--propagation','private','--','/usr/bin/python3.10','-I','-B',str(HELPER),str(path)]
    proc=subprocess.run(command,input=b'',capture_output=True,timeout=1500,close_fds=True)
    (args.out/'stdout.txt').write_bytes(proc.stdout);(args.out/'stderr.txt').write_bytes(proc.stderr)
    result={'schema':'RH_SUPPLEMENTARY_NATIVE_CACHE_COMPATIBILITY_V1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FAIL','source_spec':str(args.spec.resolve()),'source_spec_sha256':sha(args.spec),'canary_source_sha256':sha(__file__),'helper_sha256':sha(HELPER),'command':command,'returncode':proc.returncode,'remote_inference':False,'mathematical_validity':'NOT_INFERRED_FROM_IMPORT_COMPATIBILITY','does_not_modify_original_preflight':True,'env':spec['env']}
    if proc.returncode==0:result.update(json.loads(proc.stdout))
    target=args.out/'RESULT.json';temporary=args.out/'RESULT.pending';temporary.write_text(json.dumps(result,indent=2)+'\n');os.link(temporary,target);temporary.unlink()
    print(json.dumps({'status':result['status'],'receipt':str(target)}))
    if result['status']!='PASS_NATIVE_CACHE_IMPORT_COMPATIBILITY':raise SystemExit(1)

if __name__=='__main__':main()
