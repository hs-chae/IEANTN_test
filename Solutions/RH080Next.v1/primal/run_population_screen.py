#!/usr/bin/env python3
"""Deterministic bounded floating scouting. Never an acceptance validator."""
import argparse,concurrent.futures,hashlib,json,os,shutil,subprocess,sys,time
from pathlib import Path

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--workers',type=int,default=4);ap.add_argument('--meshes',default='8,16,32');ap.add_argument('--radii',default='2,3,5,7');args=ap.parse_args()
 if args.out.exists():raise ValueError('Fresh output directory required')
 args.out.mkdir(parents=True);source=Path(__file__).resolve().parent;frozen=args.out/'source';frozen.mkdir()
 for name in ['run_population_screen.py','search_affine_population_lp.py','floating_trig.c']:shutil.copy2(source/name,frozen/name)
 meshes=[int(z)for z in args.meshes.split(',')];radii=[int(z)for z in args.radii.split(',')]
 if not meshes or not radii or any(z<1 for z in meshes+radii):raise ValueError('Positive mesh and radius integers required')
 plan=[(m,R,A)for m in meshes for R in radii for A in ['3.2727272727272727272727','4.00001']]
 def run(case):
  m,R,A=case;label=f'm{m}-r{R}-A'+('36d11'if A.startswith('3.')else'400001d100000');out=args.out/label
  cmd=[sys.executable,str(frozen/'search_affine_population_lp.py'),'--m',str(m),'--radius',str(R),'--A',A,'--alpha','1','--grid','2048','--review-grid','65536','--out',str(out),'--threads','2']
  began=time.monotonic()
  with (args.out/(label+'.stdout')).open('w')as so,(args.out/(label+'.stderr')).open('w')as se:
   proc=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=so,stderr=se)
  result={'case':label,'exit_code':proc.returncode,'seconds':time.monotonic()-began,'command':cmd}
  if (out/'RESULT.json').exists():
   r=json.loads((out/'RESULT.json').read_text());result.update({key:r[key]for key in ['ratio','norm','maxW_exact','J_exact']})
  print(json.dumps(result),flush=True);return result
 with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers)as ex:results=list(ex.map(run,plan))
 report={'status':'FLOATING_SCREEN_NOT_THEOREM_CERTIFICATE_OR_PV','plan':plan,'results':results,'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in frozen.iterdir()},'python':sys.version}
 (args.out/'RESULT.json').write_text(json.dumps(report,indent=2)+'\n')
 if any(r['exit_code']!=0 for r in results):raise SystemExit(1)
if __name__=='__main__':main()
