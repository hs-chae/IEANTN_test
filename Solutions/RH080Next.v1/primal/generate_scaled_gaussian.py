#!/usr/bin/env python3
"""Generate new exact Gaussian cell proofs, reusing unchanged old generic checker.

This is deterministic certificate generation, never Lean acceptance or PV.
"""
import argparse,hashlib,json,subprocess,sys,time
from fractions import Fraction as Q
from pathlib import Path

def need(v,m):
 if not v:raise ValueError(m)
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--denom',type=int,default=32);ap.add_argument('--root-denom',type=int,default=32768);ap.add_argument('--chunk-size',type=int,default=32);a=ap.parse_args()
 need(not a.out.exists(),'Fresh output required');a.out.mkdir(parents=True);start=time.monotonic();old=Path(__file__).resolve().parents[2]/'RH080Study.v1/functional/primal40';sys.path.insert(0,str(old));import prototype_cells as pc;import generate_kernel_cells as gc
 dat=json.loads(a.candidate.read_text());s=Q(str(dat['scale']));need(s==Q(5,4),'Frozen scale5/4');p,q=gc.source_polynomials(dat);need(len(p)==81 and len(q)==81,'Physical degree80');need(p[0]==1,'Exact F(0)=1')
 left=Q(1772453850905,10**12)/s;packet={}
 for name,source,begin,kind in [('norm',p,Q(0),'abs'),('wing',q,left,'positive')]:
  cells=[]
  def refine(x,y):
   c=pc.cell(source,x,y,8,kind)
   if c['sgn']==0 and y-x>Q(1,a.root_denom):
    z=(x+y)/2;refine(x,z);refine(z,y)
   else:cells.append(c)
  x=begin
  while x<12:
   y=min(Q(12),x+Q(1,a.denom));refine(x,y);x=y
  total=sum((c['upper']for c in cells),Q(0));packet[name]={'cells':cells,'raw_half_integral_upper':total};print(json.dumps({'family':name,'cells':len(cells),'raw_upper':float(total),'physical_upper_diagnostic':float(total*Q('1.128379167096')/(s if name == 'norm' else 1)),'seconds':time.monotonic()-start}),flush=True)
 packet['status']='GENERATED_NOT_LEAN_ACCEPTANCE';packet['parameters']={'denom':a.denom,'root_denom':a.root_denom,'scale':str(s),'wing_lower':str(left),'cutoff':12,'taylor_terms':8}
 partition=a.out/'PARTITION.json';partition.write_text(json.dumps(pc.encode(packet),indent=2)+'\n')
 cmd=[sys.executable,str(old/'generate_kernel_cells.py'),'--candidate',str(a.candidate),'--partition',str(partition),'--output',str(a.out/'raw'),'--chunk-size',str(a.chunk_size)]
 subprocess.run(cmd,check=True)
 target=a.out/'source';target.mkdir();raw=a.out/'raw';sources=[]
 for f in sorted(raw.glob('*.lean')):
  name=f.name.replace('GaussianSources','Scaled40Sources').replace('GaussianCells','Scaled40Cells')
  text=f.read_text().replace('import GaussianCertificate','import G40Certificate').replace('import GaussianSources','import Scaled40Sources').replace('namespace RHOnePrime.GaussianKernel','namespace RH080Next.Scaled40\nopen RH080.Gaussian40').replace('end RHOnePrime.GaussianKernel','end RH080Next.Scaled40')
  f2=target/name;f2.write_text(text);sources.append({'file':name,'sha256':hashlib.sha256(f2.read_bytes()).hexdigest(),'bytes':f2.stat().st_size})
 (a.out/'CANDIDATE.json').write_bytes(a.candidate.read_bytes());result={'status':'GENERATED_NOT_LEAN_ACCEPTANCE','sources':sources,'candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'partition_sha256':hashlib.sha256(partition.read_bytes()).hexdigest(),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'reused_generator_sha256':hashlib.sha256((old/'generate_kernel_cells.py').read_bytes()).hexdigest(),'reused_arithmetic_sha256':hashlib.sha256((old/'prototype_cells.py').read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'command':sys.argv};(a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'seconds':result['seconds'],'sources':len(sources)}),flush=True)
if __name__=='__main__':main()
