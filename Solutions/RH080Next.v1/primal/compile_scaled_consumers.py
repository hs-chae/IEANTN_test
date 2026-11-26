#!/usr/bin/env python3
"""Fresh-source development replay of scaled Gaussian assemblies and consumers.

Generic/prerequisite object paths are explicit. A complete cold source closure
is a separate gate; this receipt never calls this replay source-first PV.
"""
import argparse,hashlib,json,os,re,shutil,subprocess,sys,time
from pathlib import Path

def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--compiler',type=Path,required=True);ap.add_argument('--lean-path',required=True);ap.add_argument('--cell-run',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--wait-seconds',type=int,default=0);a=ap.parse_args();need(not a.out.exists(),'Fresh run required');a.out.mkdir(parents=True);here=Path(__file__).resolve().parent/'scaled40';began=time.monotonic();names=['Scaled40FiniteNorm','Scaled40FiniteWing','Scaled40FullRays','Scaled40Physical','Scaled40Wings','Scaled40Consumers'];frozen=a.out/'source';objects=a.out/'objects';logs=a.out/'logs'
 for p in [frozen,objects,logs]:p.mkdir()
 for name in names:shutil.copy2(here/(name+'.lean'),frozen/(name+'.lean'))
 while not (a.cell_run/'RESULT.json').exists():
  need(time.monotonic()-began<a.wait_seconds,'Cell acceptance receipt absent; check preserved run status')
  time.sleep(min(5,a.wait_seconds))
 cr=json.loads((a.cell_run/'RESULT.json').read_text());need(cr['status']=='PASS_EXPLICIT_SELECTED_CELL_COMPILATION','Cell proofs did not all pass');need(len(cr['actual_runs'])==36 and all(r['accepted']for r in cr['actual_runs']),'Exact36 kernel chunks required')
 env=dict(os.environ,LEAN_PATH=str(objects.resolve())+':'+str((a.cell_run/'objects').resolve())+':'+a.lean_path);allowed={'propext','Classical.choice','Quot.sound'};rows=[]
 for name in names:
  p=frozen/(name+'.lean');expected=p.read_text().count('#print axioms');need(expected>0,'Axiom audit mandatory');cmd=['prlimit','--as='+str(32*2**30),'--','/usr/bin/time','-v','-o',str((logs/(name+'.time')).resolve()),str(a.compiler.resolve()),'-j','1','-o',str((objects/(name+'.olean')).resolve()),p.name];t=time.monotonic();r=subprocess.run(cmd,cwd=frozen,env=env,text=True,capture_output=True);(logs/(name+'.stdout')).write_text(r.stdout);(logs/(name+'.stderr')).write_text(r.stderr);audits=re.findall(r'depends on axioms: \[([^\]]*)\]',r.stdout);peaks=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',(logs/(name+'.time')).read_text());output=objects/(name+'.olean');valid=r.returncode==0 and len(audits)==expected and all({x.strip()for x in row.split(',')if x.strip()}<=allowed for row in audits) and len(peaks)==1 and output.is_file() and sha(here/p.name)==sha(p)
  row={'module':name,'accepted':valid,'returncode':r.returncode,'command':cmd,'seconds':time.monotonic()-t,'source_sha256':sha(p),'object_sha256':sha(output)if output.is_file()else None,'axiom_audits':len(audits),'expected_audits':expected,'peak_RSS_KiB':int(peaks[0])if len(peaks)==1 else None};rows.append(row);print(json.dumps(row),flush=True)
  if not valid:
   (a.out/'FAILED.json').write_text(json.dumps({'status':'FAILED_NO_ACCEPTANCE','rows':rows},indent=2)+'\n');print(r.stdout,r.stderr);raise ValueError('Consumer compilation or audit failed')
 result={'status':'PASS_SCALED_GAUSSIAN_ACTUAL_INTEGRALS_FOURIER_AND_CMS_CONSUMERS_STD3','scope':'Development prerequisite objects disclosed; complete cold closure separate. Kernel-only proof, not PV.','rows':rows,'compiler_sha256':sha(a.compiler),'script_sha256':sha(Path(__file__)),'cell_receipt_sha256':sha(a.cell_run/'RESULT.json'),'LEAN_PATH':env['LEAN_PATH'],'seconds':time.monotonic()-began};p=a.out/'RESULT.pending';p.write_text(json.dumps(result,indent=2)+'\n');os.link(p,a.out/'RESULT.json');p.unlink()
if __name__=='__main__':main()
