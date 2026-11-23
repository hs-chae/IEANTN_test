#!/usr/bin/env python3
"""Independent seven-source Ram620 review with explicitly reused foundation.

This is an incremental reviewer replay, not the final complete source gate.
"""
from pathlib import Path
import argparse,json,os,re,resource,subprocess,time
from reproduce import read,save,need,sha,audit,COMPILER_SHA
B=Path(__file__).resolve().parent;N=B.parents[2];S=B.parent/'spectral'
D=Path('/data/ivy-rh-limit-20261122/spectral');OLD=Path('/data/ivy-rh-continuation-20261122/ramanujan')
MODS=['Ram620Low','Ram620Anchors','Ram620Powers','Ram620Bands','Ram620Finite','Ram620Leaves','Ram620Result']
BANKS=[OLD/'node-publication-v9/objects',OLD/'strong-source-v2/objects',OLD/'strong-source-v2/union',D/'refined-v4/objects']
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve()
 need(not out.exists(),'fresh output');ctx=read(N/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json');need(sha(ctx['compiler'])==COMPILER_SHA,'compiler pin')
 old=read(D/'ram-result-v2/RESULT.json');need(old['status']=='PASS','accepted prior foundation receipt');bp=D/'ram-result-v2/BANK_SNAPSHOT.json';need(sha(bp)==old['current_bank_snapshot_sha256'],'foundation receipt association')
 expected={r['file']:r['sha256']for r in read(bp)};foundation=[]
 for bank in BANKS:
  for obj in bank.rglob('*.olean'):
   need(sha(obj)==expected[str(obj)],'foundation object drift');foundation.append({'file':str(obj),'sha256':sha(obj)})
  for mod in MODS:need(not (bank/(mod+'.olean')).exists(),'review module leaked into foundation')
 manifest={r['module']:r for r in read(S/'RAM620_RESULTS.json')['module_records']};out.mkdir();(out/'source').mkdir();(out/'objects').mkdir();(out/'logs').mkdir();save(out/'FOUNDATION.json',foundation)
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out/'objects'),*map(str,BANKS),*ctx['generic_libraries']]);start=time.monotonic();rows=[]
 for mod in MODS:
  orig=S/(mod+'.lean');need(sha(orig)==manifest[mod]['source_sha256'],'author source pin');src=out/'source'/orig.name;src.write_bytes(orig.read_bytes());obj=out/'objects'/(mod+'.olean')
  ns=re.search(r'^namespace (\S+)',src.read_text(),re.M).group(1);roots=[ns+'.'+n for n in re.findall(r'^#print axioms (\S+)',src.read_text(),re.M)]
  cmd=[ctx['compiler'],'--root='+str(out/'source'),'-j8','-o',str(obj),str(src)];st=time.monotonic();run=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=out/'source',env=env,text=True,capture_output=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(80*1024**3,80*1024**3)))
  (out/'logs'/(mod+'.stdout')).write_text(run.stdout);(out/'logs'/(mod+'.stderr')).write_text(run.stderr)
  row={'module':mod,'returncode':run.returncode,'command':cmd,'source_sha256':sha(src),'seconds':time.monotonic()-st,'peak_RSS_KiB':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',run.stderr).group(1))};rows.append(row);save(out/'BUILD.json',{'status':'RUNNING'if run.returncode==0 else'FAIL','modules':rows})
  need(run.returncode==0,'independent compile failed:'+mod);need(sha(src)==sha(orig),'source changed during review');row['object_sha256']=sha(obj);row['axiom_audits']=audit(run.stdout,roots);print('PASS',mod,flush=True)
 for row in foundation:need(sha(Path(row['file']))==row['sha256'],'foundation changed during replay')
 save(out/'BUILD.json',{'status':'PASS','modules':rows});save(out/'RESULT.json',{'status':'PASS_INDEPENDENT_SEVEN_SOURCE_RAM620_RECOMPILATION','reviewer':'octicworker distinct from spectral proofauthor','scope':'Seven new Ram620 modules only; explicit source/object-pinned predecessor foundation reused, not full source closure.','compiler_sha256':COMPILER_SHA,'controller_sha256':sha(__file__),'seconds':time.monotonic()-start,'foundation_sha256':sha(out/'FOUNDATION.json'),'modules':rows,'source_first_PV':False,'full_source_replay':False})
if __name__=='__main__':main()
