"""Exact-rational data generator; every generated fact must still be checked by Lean.
The baseline CLI only instantiates M0. This frozen generic function may later be reused.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal,localcontext
import math,struct,json,time,hashlib

def rat(q):
 q=F(q);return str(q.numerator) if q.denominator==1 else '('+str(q.numerator)+'/'+str(q.denominator)+')'
def literal(q):
 with localcontext() as ctx:
  ctx.prec=1200;s=format(Decimal(q.numerator)/Decimal(q.denominator),'f')
  return s if '.' in s else s+'.0'
def upward(q):
 f=float(q)
 if F.from_float(f)<q:f=math.nextafter(f,math.inf)
 return F.from_float(f)
def create(qroot,module,namespace,m,M,*,A=3914,Y=3915,n=7,bound=F('3914.7'),label='baseline'):
 t=time.perf_counter();m,M,A,Y=map(F,[m,M,A,Y]);N=max(0,-m);P=max(0,m)
 targets=[2*M,(2*M+132)/Y,(4*M+288)/Y**2,(12*M+576)/Y**3,48*M/Y**4,M**2/Y**5,N*(1+1/A)**6]
 if not 1<=n<=7:raise ValueError('only preregistered grouping family1..7')
 groups=[sum(targets[(7*j)//n:(7*(j+1))//n],F()) for j in range(n)]
 vals=[upward(max(v/F(4096),F(1,2**40))) for v in groups]
 if any(not F(1,2**40)<=v<=1 for v in vals):raise ValueError('unsupported input range')
 literals=list(map(literal,vals));floats=list(map(float,vals));s=0.0
 for v in floats:s=s+v
 r0=s*4096.0;r1=r0-134.0;out=r1-float(P);bits=struct.unpack('>Q',struct.pack('>d',out))[0]
 # The generator's FP output is a diagnostic candidate; the operational Lean theorem is authoritative.
 stem=module.split('.')[-1];source_name=label+'.c';p=qroot/'c'/source_name;p.parent.mkdir(exist_ok=True)
 prefix='''double sum(const double *a, unsigned n) {
    double s = 0.0;
    for (unsigned i = 0; i < n; ++i) {
        s += a[i];
    }
    return s;
}
'''
 source=prefix+'\nstatic const double inputs['+str(n)+'] = {\n    '+',\n    '.join(literals)+'\n};\ndouble ramanujan_epsilon_bound(void) {\n    double s = sum(inputs, '+str(n)+');\n    double r = (s * 4096.0);\n    r = (r - 134.0);\n    r = (r - '+literal(P)+');\n    return r;\n}\n';p.write_text(source)
 header='/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\n'
 s=header+'''import ForwardRamanujan.Math
import ForwardRamanujan.Source

namespace NAMESPACE
open Real IEANTN FKS2Scalar FKS2Table4 SumStability ForwardRamanujan
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def m : ℚ := MLOW
def M : ℚ := MUP
def A : ℚ := AVAL
def Y : ℚ := YVAL
def targets : List ℚ := [TARGETS]
def literals : List String := [LITERALS]
def data : List ℚ := literals.map fun s => (loadLiteral s).getD 0
def program : ForwardRamanujan.Program := ⟨literals,"4096.0","134.0","POSLIT"⟩
def actualSource : String := include_str ".."/"c"/"SOURCENAME"
def initial : CState := FKS2SumBridge.sumInitial data
def sumOut : ℚ := (runSum data 0).getD 0
def outputBits : ℕ := OUTPUTBITS
def out : ℚ := decodeBits outputBits
def scale : ℚ := 4096
def fixedOffset : ℚ := 134
def positiveOffset : ℚ := POSVAL
def r0 : ℚ := (round64 (sumOut*scale)).getD 0
def r1 : ℚ := (round64 (r0-fixedOffset)).getD 0
def suffixError : ℚ := 1/10^10
def totalError : ℚ := forwardError scale sumOut suffixError data.length
def bound : ℚ := BOUND

theorem source_check : sourceMatches actualSource program=true := by native_decide

theorem enclosure_check : data.length=NLEN ∧ targets.length=7 ∧
    (∀ j ∈ Finset.range NLEN, (GROUPLIST)[j]!/4096 ≤ data[j]!) ∧
    (∀ j ∈ Finset.range NLEN, if (GROUPLIST)[j]!/4096 < 1/2^40 then data[j]! =1/2^40 else True) ∧
    targets.sum ≤ scale*data.sum := by native_decide

theorem domain_check : ∀ r ∈ data,FKS2SumBridge.inputCheck r=true := by native_decide

theorem execution_check : program.inputs.mapM loadLiteral=some data ∧
    RepresentsInput initial data ∧ runSum data 0=some sumOut ∧
    chainCheck data 0 sumOut=true ∧ suffix program sumOut=some out ∧
    finiteBits outputBits=true ∧ encodePositiveNormal out=some outputBits := by
  unfold RepresentsInput
  native_decide

theorem suffix_check : loadLiteral program.scale=some scale ∧
    loadLiteral program.fixedOffset=some fixedOffset ∧
    loadLiteral program.positiveOffset=some positiveOffset ∧
    additionCheck (sumOut*scale) r0=true ∧
    additionCheck (r0-fixedOffset) r1=true ∧
    additionCheck (r1-positiveOffset) out=true ∧
    r0=scale*sumOut ∧
    |r1-(r0-fixedOffset)|≤1/10^11 ∧
    |out-(r1-positiveOffset)|≤1/10^11 := by native_decide

theorem budget_check : (data.map abs).sum=data.sum ∧
    0≤gamma (data.length-1) ∧ gamma (data.length-1)<1 ∧
    0≤scale ∧ 0≤totalError ∧ totalError≤1/10^8 ∧
    out+totalError≤bound := by native_decide

theorem suffix_roundoff : |out-(scale*sumOut-fixedOffset-positiveOffset)|≤suffixError := by
  have h1 := abs_le.mp suffix_check.2.2.2.2.2.2.2.1
  have h2 := abs_le.mp suffix_check.2.2.2.2.2.2.2.2
  rw [suffix_check.2.2.2.2.2.2.1] at h1
  rw [abs_le]
  unfold suffixError
  constructor <;> linarith

theorem suffix_IEEE : ForwardRamanujan.SuffixIEEE program sumOut out := by
  exact ⟨scale,fixedOffset,positiveOffset,r0,r1,
    suffix_check.1,suffix_check.2.1,suffix_check.2.2.1,
    additionCheck_sound suffix_check.2.2.2.1,
    additionCheck_sound suffix_check.2.2.2.2.1,
    additionCheck_sound suffix_check.2.2.2.2.2.1⟩

theorem concrete_execution : Exec actualSource program initial out := by
  obtain ⟨final,hkernel⟩ := ForwardRamanujan.kernel_from_chain execution_check.2.2.2.1
    (show data.length≤64 by rw [enclosure_check.1];norm_num)
  exact ⟨source_check,by decide,by decide,data,sumOut,final,execution_check.1,
    execution_check.2.1,execution_check.2.2.1,hkernel,execution_check.2.2.2.2.1,suffix_IEEE⟩

/-- Domain evidence is a parameter so an independently checked kernel certificate can replace it. -/
theorem verified_with_domain (hd : ValidInputs data) {q : ℚ}
    (he : Exec actualSource program initial q) :
    (targets.sum:ℝ)-(fixedOffset:ℝ)-(positiveOffset:ℝ)≤(q:ℝ)+(totalError:ℝ) := by
  have hn : 1≤data.length ∧ data.length≤64 := by rw [enclosure_check.1];norm_num
  have hg : (gamma (data.length-1):ℝ)<1 := by exact_mod_cast budget_check.2.2.1
  have href : (targets.sum:ℝ)≤(scale:ℝ)*(data.sum:ℝ) := by
    exact_mod_cast enclosure_check.2.2.2.2
  have hf : |(out:ℝ)-((scale:ℝ)*(sumOut:ℝ)-(fixedOffset:ℝ)-(positiveOffset:ℝ))|≤(suffixError:ℝ) := by
    exact_mod_cast suffix_roundoff
  exact source_linked_upper he execution_check.1 execution_check.2.2.1
    execution_check.2.2.2.2.1 hn hd budget_check.1 hg budget_check.2.2.2.1 href hf

theorem checked_domain : ValidInputs data := by
  intro r hr
  exact FKS2SumBridge.inputCheck_sound (domain_check r hr)

theorem verified_transport {q : ℚ} (he : Exec actualSource program initial q) :
    (targets.sum:ℝ)-(fixedOffset:ℝ)-(positiveOffset:ℝ)≤(q:ℝ)+(totalError:ℝ) :=
  verified_with_domain checked_domain he

theorem selected_execution_witness : ∃ q : ℚ, Exec actualSource program initial q ∧
    (targets.sum:ℝ)-(fixedOffset:ℝ)-(positiveOffset:ℝ)≤(q:ℝ)+(totalError:ℝ) :=
  ⟨out,concrete_execution,verified_transport concrete_execution⟩

theorem terms_cast : (targets.sum:ℝ)=(terms (m:ℝ) (M:ℝ) (A:ℝ) (Y:ℝ)).sum := by
  norm_num [targets,terms,m,M,A,Y,List.sum_cons,List.sum_nil]

theorem upper_as_targets : upper (m:ℝ) (M:ℝ) (A:ℝ) (Y:ℝ)=
    (targets.sum:ℝ)-(fixedOffset:ℝ)-(positiveOffset:ℝ) := by
  rw [upper,←terms_cast]
  norm_num [m,fixedOffset,positiveOffset]

theorem certified_upper_with_domain (hd : ValidInputs data) :
    upper (m:ℝ) (M:ℝ) (A:ℝ) (Y:ℝ)≤(bound:ℝ) := by
  rw [upper_as_targets]
  have h := verified_with_domain hd concrete_execution
  have hb : (out:ℝ)+(totalError:ℝ)≤(bound:ℝ) := by
    exact_mod_cast budget_check.2.2.2.2.2.2
  exact h.trans hb

theorem certified_upper : upper (m:ℝ) (M:ℝ) (A:ℝ) (Y:ℝ)≤(bound:ℝ) :=
  certified_upper_with_domain checked_domain

theorem epsilon_bound : ∀ x>exp (Y:ℝ),
    DudekPlatt.v3.εUpper (M:ℝ) x-DudekPlatt.v3.εLower (m:ℝ) (exp (A:ℝ)) x≤(bound:ℝ) := by
  intro x hx
  have hY : (0:ℝ)<(Y:ℝ) := by norm_num [Y]
  have hM : (0:ℝ)≤(M:ℝ) := by norm_num [M]
  have hlog : (Y:ℝ)≤log x := by
    have ht := log_lt_log (exp_pos (Y:ℝ)) hx
    rw [log_exp] at ht
    exact ht.le
  exact (epsilon_majorant hM hY hlog).trans certified_upper
end NAMESPACE
'''
 replacements={'NAMESPACE':namespace,'MLOW':rat(m),'MUP':rat(M),'AVAL':rat(A),'YVAL':rat(Y),'TARGETS':','.join(map(rat,targets)),'LITERALS':','.join(json.dumps(v) for v in literals),'POSLIT':literal(P),'POSVAL':rat(P),'SOURCENAME':source_name,'OUTPUTBITS':hex(bits),'BOUND':rat(bound),'NLEN':str(n),'GROUPLIST':'(['+','.join(map(rat,groups))+'] : List ℚ)'}
 for key,value in replacements.items():s=s.replace(key,value)
 dest=qroot/Path(*module.split('.')).with_suffix('.lean');dest.parent.mkdir(exist_ok=True);dest.write_text(s)
 return {'label':label,'module':module,'namespace':namespace,'m':str(m),'M':str(M),'A':str(A),'Y':str(Y),'group_count':n,'target_count':7,'targets':[str(t) for t in targets],'groups':[str(g) for g in groups],'array':[{'index':j,'literal':lit,'exact_loaded':str(v),'bits':format(struct.unpack('>Q',struct.pack('>d',float(v)))[0],'016x'),'target_group':str(g),'floor_active':g/F(4096)<F(1,2**40)} for j,(lit,v,g) in enumerate(zip(literals,vals,groups))],'output_bits':format(bits,'016x'),'output_diagnostic':format(out,'.17g'),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lean_sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),'generator_seconds':time.perf_counter()-t,'bound':str(bound),'FP_operations':n+3,'disclosure':'Generator diagnostics are not a proof; source execution and all input/rounding claims must pass the generated Lean theorem.'}
if __name__=='__main__':
 Q=Path(__file__).resolve().parent;X=Q.parents[2];record=create(Q,'ForwardRamanujan.Old','ForwardRamanujan.Old',-1194,1426)
 (X/'evidence/old-generated-data.json').write_text(json.dumps(record,indent=2)+'\n');print('M0 generated',record['output_bits'],record['output_diagnostic'])
