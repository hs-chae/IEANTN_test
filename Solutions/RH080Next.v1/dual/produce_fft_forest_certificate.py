"""Untrusted exact-integer trace proposer. No output is accepted without Lean checks."""
from pathlib import Path
from hashlib import sha256
import argparse,json,time
R=Path(__file__).resolve().parents[3]
p=argparse.ArgumentParser();p.add_argument('--stages',type=int,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
if not 10 <= a.stages <= 17: raise ValueError('Diagnostic/full Fap stages must be 10..17')
if a.out.exists(): raise FileExistsError('Fresh destination required')
src=R/'Solutions/RH080Study.v1/ablation/followup/independent-global-chord/inputs/witness-ap.json'
if sha256(src.read_bytes()).hexdigest()!='9f545a294f104a1baaeccbb9bf625f6338fc020af9dce9ff7bd34352630a586a': raise ValueError('Locked Fap input hash changed')
d=json.loads(src.read_text());U=10**36;PI=3141592653589793238462643383279502884
if d['m']!=80 or d['scale']!=10**12 or len(d['coefficients'])!=400 or any(type(x) is not int for x in d['coefficients']): raise ValueError('Locked input shape')
a.out.mkdir();t=time.monotonic();n=2**a.stages;coeff=[x*10000 for x in d['coefficients']]
def root(n):
 x=2*PI//n;x2=x*x//U;ct=cr=U;st=sr=x
 for i in range(1,11):
  ct=(ct*x2//U)//(2*i*(2*i-1));st=(st*x2//U)//(2*i*(2*i+1))
  cr+=(-1 if i%2 else 1)*ct;sr+=(-1 if i%2 else 1)*st
 return(cr,-sr)
def mul(a,b):return(a[0]*b[0]//U-a[1]*b[1]//U,a[0]*b[1]//U+a[1]*b[0]//U)
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def sub(a,b):return(a[0]-b[0],a[1]-b[1])
def ceil(a,b):return(a+b-1)//b
def integer(v):return f'(Int.ofNat {v})' if v>=0 else f'(Int.negSucc {-v-1})'
def pair(z):return f'({integer(z[0])},{integer(z[1])})'
seed=root(n);tw=[(U,0)]
for i in range(n//2-1):tw.append(mul(tw[-1],seed))
files=[]
def payload(name,values):
 p=a.out/name
 with p.open('x') as f:
  for x,y in values:f.write(f'{x},{y}\n')
 files.append({'file':name,'sha256':sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size});return p
ns=f'FapForest{a.stages}'
header='set_option maxRecDepth 2000000\nset_option maxHeartbeats 0\nnoncomputable section\n'
wtext='import FFTUntrustedData\nimport FFTForestTrace\n'+header+f'namespace {ns}\nopen RH080Next.FFT.IntegerModel\ndef seed : CInt := {pair(seed)}\n'
for level in range(1,a.stages+1):
 ws=[tw[j*(n//2**level)] for j in range(2**(level-1))];payload(f'w-{level:02}.csv',ws)
 wtext+=f'pair_certificate w{level:02} from "w-{level:02}.csv" count {len(ws)}\n'
wtext+='def stages : Nat → List CInt\n  | 0 => []\n'+''.join(f'  | {s} => w{s:02}\n' for s in range(1,a.stages+1))+'  | _ => []\n'
wtext+=f'def leaves : List (List CInt) := (List.range {n}).map (fun j => [input {n} j])\nend {ns}\n'
(a.out/'ForestTables.lean').write_text(wtext)
wcheck='import ForestTables\n'+header+f'namespace {ns}\nopen RH080Next.FFT.IntegerModel\ntheorem twiddles_checked : checkTwiddles seed (unit,0) w{a.stages:02}.tail=true := by decide +kernel\ntheorem global_twiddle_trace : TwiddleTrace seed (unit,0) w{a.stages:02}.tail := checkTwiddles_sound _ _ _ twiddles_checked\n'
for s in range(1,a.stages):
 wcheck+=f'theorem decimation{s:02} : EvenTrace w{s+1:02} w{s:02} := checkEvens_sound _ _ (by decide +kernel)\n'
wcheck+='#print axioms global_twiddle_trace\n'+''.join(f'#print axioms decimation{s:02}\n'for s in range(1,a.stages))+f'end {ns}\n'
(a.out/'ForestTablesCheck.lean').write_text(wcheck)
def inp(j):
 k=j if j<400 else n-j
 return(coeff[k]*10**20,0) if k<400 else(0,0)
previous=[[inp(j)] for j in range(n)]
for level in range(1,a.stages+1):
 count=n//2**level;half=2**(level-1);ws=[tw[j*(n//2**level)]for j in range(half)];out=[]
 for index in range(count):
  av=previous[index];bv=previous[index+count];products=[mul(y,w)for y,w in zip(bv,ws)]
  out.append([add(x,y)for x,y in zip(av,products)]+[sub(x,y)for x,y in zip(av,products)])
 payload(f'layer-{level:02}.csv',(z for row in out for z in row))
 (a.out/f'ForestData{level:02}.lean').write_text('import FFTUntrustedData\n'+header+f'namespace {ns}\nforest_certificate out{level:02} from "layer-{level:02}.csv" width {2**level} rows {count}\nend {ns}\n')
 prev=f'out{level-1:02}' if level>1 else 'leaves';imports=f'import ForestData{level-1:02}\n'if level>1 else ''
 text='import ForestTables\n'+imports+f'import ForestData{level:02}\n'+header+f'namespace {ns}\nopen RH080Next.FFT.IntegerModel\ntheorem layer{level:02}_checked : checkLayer w{level:02} ({prev}.take {count}) ({prev}.drop {count}) out{level:02}=true := by\n  decide +kernel\ntheorem layer{level:02}_trace : LayerTrace w{level:02} ({prev}.take {count}) ({prev}.drop {count}) out{level:02} := checkLayer_sound _ _ _ _ layer{level:02}_checked\n#print axioms layer{level:02}_trace\nend {ns}\n'
 (a.out/f'ForestCheck{level:02}.lean').write_text(text);previous=out
values=previous[0];total=sum(abs(z[0])for z in values);quad=sum(20*j*j*abs(v)for j,v in enumerate(coeff));numerator=ceil(ceil(total,10**18),n)+ceil(ceil(ceil(100*quad,3),n),n)+20
expected={10:1186010558078384875,14:783336421502930946,17:781796015790084776}
if a.stages in expected and numerator!=expected[a.stages]:raise ValueError('Actual model/C native crosscheck differs')
text='import ForestTablesCheck\n'+''.join(f'import ForestCheck{s:02}\n'for s in range(1,a.stages+1))+header+f'namespace {ns}\nopen RH080Next.FFT.IntegerModel\ntheorem complete_forest : ForestTrace stages (input {n}) {a.stages} 1 0 out{a.stages:02} := by\n  have h0 : ForestTrace stages (input {n}) 0 {n} 0 leaves := leaf_forest stages (input {n}) {n} {n}\n'
for s in range(1,a.stages+1):
 count=n//2**s;prev=f'out{s-1:02}'if s>1 else 'leaves'
 text+=f'  have h{s} : ForestTrace stages (input {n}) {s} {count} 0 out{s:02} := layer_step h{s-1} (by decide +kernel) layer{s:02}_trace\n'
text+=f'  exact h{a.stages}\ndef output : List CInt := out{a.stages:02}.head!\ntheorem complete_execution : ExecutionTrace stages (input {n}) {a.stages} 0 1 output := singleton_execution complete_forest\ndef totalAbs : Nat := output.foldl (fun a z => a+z.1.natAbs) 0\ntheorem total_checked : totalAbs={total} := by decide +kernel\ndef quad : Nat := (List.range 400).foldl (fun a j => a+20*j*j*(coefficient j).natAbs) 0\ntheorem quad_checked : quad={quad} := by decide +kernel\ndef sourceNumerator : Nat := ceilDiv (ceilDiv totalAbs 1000000000000000000) {n} + ceilDiv (ceilDiv (ceilDiv (100*quad) 3) {n}) {n} + 20\ntheorem numerator_checked : sourceNumerator={numerator} := by\n  unfold sourceNumerator\n  rw [total_checked,quad_checked]\n  decide +kernel\n#print axioms complete_execution\n#print axioms numerator_checked\nend {ns}\n'
(a.out/'ForestFinal.lean').write_text(text)
proofs=[{'file':p.name,'sha256':sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}for p in sorted(a.out.glob('*.lean'))]
(a.out/'PLAN.json').write_text(json.dumps({'status':'UNTRUSTED_EXACT_INTEGER_FOREST_NOT_PROOF_NOT_PV','stages':a.stages,'n':n,'namespace':ns,'seed':seed,'norm_numerator':numerator,'total_abs':total,'quad':quad,'input_source':str(src),'input_sha256':sha256(src.read_bytes()).hexdigest(),'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'payloads':files,'lean_sources':proofs,'producer_seconds':time.monotonic()-t},indent=2)+'\n')
print(json.dumps({'stages':a.stages,'numerator':numerator,'seconds':time.monotonic()-t,'payload_bytes':sum(x['bytes']for x in files)}))
