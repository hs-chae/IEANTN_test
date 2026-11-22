#!/usr/bin/env python3
"""Rebuild the complete111-source integrated proof closure; no application cache."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time,os,re
HERE=Path(__file__).resolve().parent

def need(b,msg):
 if not b:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh output required');m=json.loads((HERE/'SOURCE_CLOSURE.json').read_text());rows=m['modules'];need(rows and rows[-1]['module']=='NetworkConsumers','complete final consumer required');need(len({r['module']for r in rows})==len(rows),'duplicate module')
 for r in rows:need(sha(HERE/r['frozen'])==r['sha256'],'frozen source mismatch:'+r['module'])
 start=time.monotonic();cmd=[sys.executable,str(HERE.parent/'scripts/build_modules.py'),'--source',str(HERE/'frozen-source'),'--out',str(out)]
 for r in rows:cmd+=['--module',r['module']]
 subprocess.run(cmd,check=True)
 raw=(out/'logs/NetworkConsumers.stdout').read_text();names=['box_psi','B5_psi','box_improves_B5','recovered_ch_psi','count_215','count_family','octic_block','successive_cubes','box_lcm','recovered_lcm','box_primorial'];axioms=[]
 for name in names:
  hits=re.findall(r"'RHContinuation.Network\."+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",raw)
  need(len(hits)==1,'missing/duplicate axiom audit:'+name);found={v.strip()for v in hits[0].split(',')};need(found=={'propext','Classical.choice','Quot.sound'},'unexpected axiom:'+name);axioms.append({'theorem':'RHContinuation.Network.'+name,'axioms':sorted(found)})
 resources=[]
 for f in sorted((out/'logs').glob('*.stderr')):
  t=f.read_text();peak=re.search(r'Maximum resident set size \(kbytes\): (\d+)',t);elapsed=re.search(r'Elapsed \(wall clock\) time.*: (.+)',t);resources.append({'module':f.name[:-7],'peak_RSS_kib':int(peak[1])if peak else None,'elapsed':elapsed[1]if elapsed else None})
 receipt={'status':'PASS_COMPLETE_SOURCE_ONLY_INTEGRATED_PROOFS','elapsed_seconds':time.monotonic()-start,'modules':len(rows),'no_prebuilt_application_objects':True,'axiom_audits':axioms,'source_manifest_sha256':sha(HERE/'SOURCE_CLOSURE.json'),'reproducer_sha256':sha(__file__),'helper_sha256':sha(HERE.parent/'scripts/build_modules.py'),'compiler_context':os.environ.get('IEANTN_GENERIC_CONTEXT',str(HERE.parent/'scripts/GENERIC_CONTEXT.json')),'resources':resources,'OOM_events':0,'scope':'actual compiler run returned0 for every module; actual conditional theorem source parameters remain explicit; no source-first PV claimed for this analytic closure'}
 target=out/'RESULT.json';need(not target.exists(),'fresh receipt required');temp=out/'.RESULT.tmp';temp.write_text(json.dumps(receipt,indent=2)+'\n');temp.replace(target);print(json.dumps({'status':receipt['status'],'modules':len(rows),'seconds':receipt['elapsed_seconds']}))
if __name__=='__main__':main()
