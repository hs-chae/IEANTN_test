"""Generate observed footer source; Lean must compare it to the source computation."""
from pathlib import Path
import argparse,hashlib,json,math,os
B=Path(__file__).resolve().parent;R=B.parents[1]
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def strict(p):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicateJSON');d[k]=v
  return d
 def bad(s):raise ValueError('nonfiniteJSON')
 def floating(s):
  v=float(s);need(math.isfinite(v),'overflowJSON');return v
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=floating,parse_constant=bad)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--run',type=Path,required=True);ap.add_argument('--source',type=Path,required=True);ap.add_argument('--receipt',type=Path,required=True);a=ap.parse_args();run=a.run.resolve();src=a.source.resolve();receipt=a.receipt.resolve();need(not src.exists()and not receipt.exists(),'fresh source/receipt');plan=strict(B/'SOURCE_PLAN_V1.json');native=strict(run/'RECEIPT.json');need(native['status']=='PASS_TWO_HIGH_ONLY_MOMENT_ENTRY_ASSOCIATIONS_AND_COMPLETE_BYTE_EQUIVALENCE_NOT_FORMAL_PROOF'and native['source_plan_sha256']==sha(B/'SOURCE_PLAN_V1.json'),'actual selected source-run association');need([r['name']for r in native['records']]==['mass','first_moment'],'both actual programs');rows=[]
 for variant,record in zip(plan['variants'],native['records']):
  need(sha(B/variant['entry'])==variant['entry_sha256']and sha(B/variant['translation_unit'])==variant['translation_unit_sha256']==record['source_sha256'],'same exact physical source unit');d=run/record['name'];raw=d/'run.stdout';data=raw.read_bytes();need(len(data)==98432 and sha(raw)==record['output_sha256'],'exact complete physical native output');tail=data[-128:];lo=int.from_bytes(tail[:64],'little');hi=int.from_bytes(tail[64:],'little');need(str(lo)==record['physical_total_low']and str(hi)==record['physical_total_high'],'exact actual footer word interpretation');rows.append(dict(name=record['name'],lo=lo,hi=hi,bytes=list(tail),raw_output_sha256=sha(raw),footer_sha256=hashlib.sha256(tail).hexdigest(),source_sha256=sha(B/variant['translation_unit']),binary_sha256=record['binary_sha256'],object_sha256=record['object_sha256']))
 text='''/- Actual selected C-output final128bytes, compared to the independently proved
source computation. The observations are not mathematical premises or certificates
replacing execution of the actual C numerical algorithms. -/
import SynergyMomentCHi.CompleteProgram
namespace SynergyMomentCHi.ObservedOutput
open ScopedNumerical SynergyMomentC SynergyHeightC
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
'''
 text+='def total : Kind→ProofBox\n'
 for row,ctor in zip(rows,['mass','firstMoment']):text+=f' | .{ctor}=>⟨{row["lo"]},{row["hi"]}⟩\n'
 text+='def bytes : Kind→List Nat\n'
 for row,ctor in zip(rows,['mass','firstMoment']):text+=' | .'+ctor+'=>['+','.join(map(str,row['bytes']))+']\n'
 text+='''theorem total_exact (kind : Kind) : FamilyAPI.total kind 768=total kind := by
 cases kind with
 | mass=>exact SourceMomentSumsV1.Data.mass_final
 | firstMoment=>exact SourceMomentSumsV1.Data.first_moment_final
theorem bytes_exact (kind : Kind) :
 bytes kind=EmitUBuffer.bytes (total kind).lo++EmitUBuffer.bytes (total kind).hi := by
 cases kind <;> decide +kernel
theorem source_bytes (kind : Kind) : bytes kind=
 EmitUBuffer.bytes (FamilyAPI.total kind 768).lo++EmitUBuffer.bytes (FamilyAPI.total kind 768).hi :=
 (bytes_exact kind).trans (congrArg
   (fun box : ProofBox=>EmitUBuffer.bytes box.lo++EmitUBuffer.bytes box.hi) (total_exact kind).symm)
#print axioms total_exact
#print axioms bytes_exact
#print axioms source_bytes
end SynergyMomentCHi.ObservedOutput
''';src.parent.mkdir(parents=True,exist_ok=True);src.write_text(text);receipt.parent.mkdir(parents=True,exist_ok=True);receipt.write_text(json.dumps(dict(status='NATIVE_FOOTER_SOURCE_PREPARED_REQUIRES_LEAN_COMPARISON',source_sha256=sha(src),source_plan_sha256=sha(B/'SOURCE_PLAN_V1.json'),native_receipt_sha256=sha(run/'RECEIPT.json'),reproducer_sha256=sha(Path(__file__)),observations=rows,qualification='Only final128bytes perprogram are directly compared in this generated Lean source. Full98432rawfiles are independently hashed; fullpointwordkernel/model/source checks are separate. This preparation is not formal or numerical acceptance.'),indent=2)+'\n')
if __name__=='__main__':main()
