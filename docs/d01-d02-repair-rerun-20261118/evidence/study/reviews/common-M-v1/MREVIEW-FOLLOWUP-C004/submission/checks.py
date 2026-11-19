from pathlib import Path
import sys, json, hashlib, re, subprocess
C=Path("/work/c004"); O=Path("/work/submission")
sys.path.insert(0,str(C))
from verify import I,F,D,piB,log,exp0,gap_cert,tail,poly
idx=json.loads(Path("/task/CANDIDATE_INDEX.json").read_text())
src=json.loads(Path("/task/SOURCE_INDEX.json").read_text())
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for r in src["sources"]:
 for k in ("pdf","text"):
  p=Path(src["root"])/r[k]; h=sha(p)
  assert h==r[k+"_sha256"]; print(r["source_id"],p,h)
for r in idx["candidate_files"]:
 p=C/r["original_name"]; q=Path("/task")/r["packet_name"]
 h=sha(p); assert h==sha(q)==r["sha256"] and p.stat().st_size==r["bytes"]
 print(q.name,p.name,h)
assert (O/"root.stdout").read_bytes()+(O/"gap.stdout").read_bytes()==(C/"gap-replay.txt").read_bytes()
for a,b in [("trade.stdout","trade-replay.txt"),("mcheck.stdout","mcheck-replay.txt"),("orders.stdout","orders-replay.txt"),("sieve.stdout","sieve-results.txt")]:
 assert (O/a).read_bytes()==(C/b).read_bytes(),(a,b)
 print("byte match",a,b)
# Exact local counterexample to literal real reading of PT Theorem 2:
n=38358837682; x=I(n)+I(".1")
R=exp0(1)*x*632207037/log(x)-1644673232**2
assert R.below(-7900000)
print("R(n+.1)",R.fmt(),"(using certified counts)")
assert exp0(F("36.6")).below(11500000000000000)
# Exact suffix comparisons, with independently re-read bin data from reproduction.
bins=[]
for line in (O/"sieve.stdout").read_text().splitlines()[2:]:
 lo,hi,s,w,z=map(int,re.findall("[0-9]+",line.replace("/10000","")))
 bins.append((lo,hi,s,w,z))
assert bins[0][0]==100000 and bins[-1][1]==195730000000
assert all(a[1]==b[0] for a,b in zip(bins,bins[1:]))
assert exp0(26).below(bins[-1][1])
for x,m,h in [(2500000,".20",".213"),(4000000,".161",".172"),(20000000,".090",".096"),(50000000,".057",".062"),(100000000,".057",".060")]:
 A=[r for r in bins if r[1]>x]
 assert A[0][0]==x
 L=log(x); u=I(max(r[-1] for r in A))/10000
 rel=u/(1-u/L**3)
 assert rel.below(m) and (I(max(r[2] for r in A))/10000).below(m) and (I(max(r[3] for r in A))/10000).below(h)
 print("suffix",x,"scaled product",rel.fmt(),"S,W",max(r[2] for r in A),max(r[3] for r in A),"/10000")
# Check numerical inequalities for written constants without changing profile tests.
assert (piB/3000000000000).below("1.05e-12")
assert (I("113.67")+1+I("1.47e-7")+I("1.78")*exp0(F(-58,6))).below(115)
assert (I(1)+I("1.47e-7")+I("1.78")*exp0(F(-21,6))).below("1.06")
for p,q,m in [(1,58,"1.04"),(F(1,2),58,F(248,115)),(F(7,8),200,"1.16"),(F(7,8),300,"1.16"),(1,21,"1.11"),(F(1,2),21,"2.48")]:
 assert (1/(I(p)-I(2)/q)).below(m)
# Same sufficient tests, not lower bounds on actual arithmetic.
for f,args in [(gap_cert,("190","190.1",[1,14],10,1)),(tail,(700,[poly[j] for j in range(19)],19))]:
 try: f(*args)
 except AssertionError as e: print("failed sufficient test",f.__name__,args,str(e))
 else: print("passes on this exact test",f.__name__,args)
print(subprocess.check_output(["/usr/bin/g++","--version"],text=True).splitlines()[0]); print(sys.version)

# Range audit of the original signed cubic path, independent of its bin maxima.
N=195730000000; H=10**8; W=1<<58; PAD=8192
gl,gh,ml,mh,wl,wh=map(int,(O/"sieve.stdout").read_text().splitlines()[0].split(": ")[1].split())
assert (1<<53)*(17*(1<<20))**3+65535 < 1<<127
assert F(".003")*W*(1<<25)**3+65535 < 1<<127
assert (log(10000020)+I(128+(1<<38))/W).below(17)
assert log(10**7).above(16)
assert max(N+mh-ml+512,3*N+wh-wl+256+2*PAD,N+520*H+W//H+1+gh-gl+512) < F("1e-5")*W
assert F(1,1<<19)+F(1,10**7)+F(1024,W) < F("3e-6")
print("Original signed cubic range ancillary checks passed")
# Cor. 9.3 domain interface: the x>=2 restriction excludes a spurious x≈1 branch.
from verify import expb
for x in [I(2),I(10**9)]:
 assert (2*piB**2*expb(log(x)/2)/log(x)).below(10**7)
x=I("1.0000001")
alt=2*piB**2*expb(log(x)/2)/log(x)
rhs=expb(log(x)/2)*log(x)**2/(8*piB)
assert alt.above(10**7) and alt.below(3000175332800) and rhs.below("1e-14")
print("Cor. 9.3 excluded small-x literal comparator",alt.fmt(),rhs.fmt())
