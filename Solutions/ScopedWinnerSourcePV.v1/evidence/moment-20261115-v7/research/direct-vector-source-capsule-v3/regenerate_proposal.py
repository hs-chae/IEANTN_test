"""One locked fixedL300 untrusted interval proposal; exactkernel must check it."""
from pathlib import Path
from fractions import Fraction as Q
import argparse,hashlib,json,re,math
B=Path(__file__).resolve().parent;R=B
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ceildiv(n,d):return -((-n)//d)
def strict(text):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicateJSON');d[k]=v
  return d
 def bad(x):raise ValueError('nonfiniteJSON')
 def floating(x):
  y=float(x);need(math.isfinite(y),'overflowJSON');return y
 return json.loads(text,object_pairs_hook=pairs,parse_float=floating,parse_constant=bad)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();dest=a.out.resolve();need(not dest.exists()and B not in dest.parents,'fresh external proposaloutput');dest.mkdir(parents=True);out=dest/'PROPOSAL_V1.json';plan=strict((B/'PLAN_V1.json').read_text());need(plan['fixed_L']==300 and plan['cells']==768 and plan['precision_bits']==128,'fixed prelaunch parameters');source=B/'base/source/SourceMomentSumsV1/Data.lean';text=source.read_text();part=text.split('def mass : List ProofBox := ',1)[1].split('\n',1)[0];mass=[(int(x),int(y))for x,y in re.findall(r'⟨(\d+),(\d+)⟩',part)];need(len(mass)==769,'all exact mass prefixes');words=[];pins=[]
 for b in range(96):
  p=B/'base/source/SourceMomentWordsV1'/f'Block{b:02d}.lean';t=p.read_text().split('def words : List (Int × Int) := ',1)[1].split('\ntheorem checked',1)[0];row=[(int(x),int(y))for x,y in re.findall(r'\((\d+),(\d+)\)',t)];need(len(row)==8,'eight exact words');words+=row;pins.append(dict(path=str(p.relative_to(R)),sha256=sha(p)))
 S=1<<128;prefix=[(0,0)]
 for i,(_,d)in enumerate(words):
  lo=mass[i+1][0]-mass[i][0];hi=mass[i+1][1]-mass[i][1];den=300*S-d;need(0<=lo<=hi and den>0,'all valid proposed denominators/masses');value=(lo*300*S//den,ceildiv(hi*300*S,den));prefix.append((prefix[-1][0]+value[0],prefix[-1][1]+value[1]))
 raw=ceildiv(prefix[-1][1]*10**12,S);tail=Q(1,250000)*300/140+Q(1,50000000)+Q(1,10**12)*300/(300-Q(880,3))+Q(1,10**12);coefficient=(1+Q(1,10**9))*(Q(1,10**12)+Q(raw,10**12)+tail)+Q(1,10**12)+Q(1,10**8);rounded=ceildiv(coefficient.numerator*10**9,coefficient.denominator)
 data='''/- One fixedL300 proposal. No output is assumed: checked below re-evaluates
all768interval terms and exact prefix recurrences in the Lean kernel. -/
import SynergyVector300.Model
namespace SynergyVector300.Data
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
'''
 data+='def totals : List ProofBox := ['+','.join('⟨'+str(lo)+','+str(hi)+'⟩'for lo,hi in prefix)+']\n'
 data+='''def total (i : Nat) : ProofBox := totals[i]?.getD ⟨0,0⟩
theorem zero : total 0=⟨0,0⟩ := rfl
theorem checked : (List.range 768).all (fun i=>decide
 (ProofBox.add (total i) (SynergyVector300.term i)=total (i+1)))=true := by decide +kernel
theorem step (i : Nat) (hi : i < 768) :
 ProofBox.add (total i) (SynergyVector300.term i)=total (i+1) :=
 of_decide_eq_true ((List.all_eq_true.mp checked) i (List.mem_range.mpr hi))
'''
 data+=f'def rawUpper : Int := {raw}\ndef roundedCoefficient : Int := {rounded}\n'
 data+='''theorem upper_word : (total 768).hi*1000000000000 ≤ rawUpper*ProofBox.scale 128 :=
 by decide +kernel
#print axioms zero
#print axioms checked
#print axioms step
#print axioms upper_word
end
end SynergyVector300.Data
'''
 target=dest/'Data.lean';need(not target.exists(),'fresh proposed source');target.write_text(data);out.write_text(json.dumps(dict(status='UNVERIFIED_FIXED300_INTERVAL_PROPOSAL_NOT_MATH_ACCEPTANCE',fixed_L=300,cells=768,mass_prefix_source_sha256=sha(source),word_sources=pins,total_low=str(prefix[-1][0]),total_high=str(prefix[-1][1]),scale=str(S),raw_upper_numerator=raw,raw_upper_denominator=10**12,rounded_coefficient_numerator=rounded,rounded_coefficient_denominator=10**9,source_sha256=sha(target),generator_sha256=sha(Path(__file__)),plan_sha256=sha(B/'PLAN_V1.json'),qualification='One predetermined rational-upper-vector interval proposal. No paired exponential evaluated; sign proof controls dropped correction. Kernel/model/ANT closure still required.'),indent=2)+'\n');print(json.dumps(dict(status='UNVERIFIED_PROPOSAL',raw_upper=raw,rounded_coefficient=rounded)))
if __name__=='__main__':main()
