import ast,hashlib,json,re,sys
from pathlib import Path
S=Path('/work/submission');C=Path('/work/c');T=Path('/task')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
j=json.loads((T/'CANDIDATE_INDEX.json').read_text())
for m in j['candidate_files']+j['support_files']:
 p=T/m['packet_name'];assert sha(p)==m['sha256'] and p.stat().st_size==m['bytes']
 if m in j['candidate_files']:assert sha(C/m['original_name'])==m['sha256']
j=json.loads((T/'SOURCE_INDEX.json').read_text())
for m in j['sources']:
 for k in ['pdf','text']:assert sha(Path(j['root'],m[k]))==m[k+'_sha256']
print('All source and candidate hashes and aliases verified.')
assert all((S/(k+'.status')).read_text().strip()=='0' for k in ['old','d02'])
ps=sorted(Path('/work/replay').glob('*_evidence.txt'));assert len(ps)==12
for p in ps:
 assert p.read_bytes()==(C/p.name).read_bytes()
 print('old byte-identical',p.name,sha(p))
actual=(S/'d02.stdout').read_text().splitlines()
for f in ['d02_basic_mid.txt','d02_centered.txt','d02_coeff.txt','d02_earliest.txt','d02_final_extras.txt','d02_rays.txt','d02_smooth.txt']:
 p=C/f
 ls=p.read_text().splitlines();assert all(l in actual for l in ls)
 print('D02 exact receipt lines',f,len(ls),sha(p))
sys.path.insert(0,str(C))
from check import I,D
from subprocess import run
r=run(['/work/small_end','38358837677','38358837682','38358837683','14111427770'],capture_output=True,check=True)
print('small_end exit',r.returncode,'stdout',repr(r.stdout),'stderr',repr(r.stderr))
for s in ['0','.1','.217926','.217927','1']:
 x=38358837682+I(s)
 v=I(1).exp()*632207037*x/x.ln()-1644673232**2
 assert (v.b<0 if D(s)<=D('.217926') else v.a>0)
 print('directed R offset',s,v)
for v in [I('.86')/I('.061')*(-I(201)/32).exp(),I('.0020012')/I('.001285')*(-I(40)/32).exp(),I('.266350')/I('.018830')*(-I(200)/32).exp()]:
 assert v.b<1
 print('matched whole-ray shape ratio at start',v)
L=I(64000000).ln()
for a,b in [('1.916','.07738'),('1.8292','.07388')]:
 v=I(a)*L**2/8000;assert v.b<D(b);print('strip scale endpoint',v,b)
rr={};cc={}
for s in actual:
 m=re.match(r'ray (\d) (basic|density) m=0\.\.205 (.*)',s)
 if m:rr[int(m[1]),m[2]]=ast.literal_eval(m[3])
 m=re.match(r'compact (\d) (\d+) (.*)',s)
 if m:cc[int(m[1]),int(m[2])]=ast.literal_eval(m[3])
assert len(rr)==4 and all(len(a)==206 for a in rr.values())
for mode in ('basic','density'):assert all(a<b for a,b in zip(rr[1,mode],rr[0,mode]))
for i,k in [(0,7),(1,10)]:
 for m in range(2,k+1):
  a,b=map(D,cc[i,m][-1]);assert b>=rr[i,'density'][m]
  print('density join',i,m,a,b,rr[i,'density'][m])
for s in actual:
 m=re.match(r'smoothed table-free compact 1 (\d+) (.*)',s)
 if m:
  k=int(m[1]);w=ast.literal_eval(m[2].replace('Decimal(','('));a,b=map(D,w[0])
  assert b>=rr[1,'basic'][k] and (k!=1 or a<D('190.8'))
  print('basic join',k,a,b,rr[1,'basic'][k])
for f in sorted(Path('/work/replay').iterdir()):
 if f.is_file():print('work/replay output or executable hash',f.name,sha(f))
print('small_end executable hash',sha(Path('/work/small_end')))
