"""Build exactly the required assigned source closure (no network)."""
from pathlib import Path
import os, re, subprocess, time, sys, concurrent.futures as cf
ORIG=Path('/representation/source')
SRC=Path('/work/relocated')
SUP=Path('/source_pv/objects')
OUT=Path('/work/objects')
SUB=Path(__file__).resolve().parent
LOG=Path('/work/buildlogs')
LOCAL={p.stem:p for p in SUB.glob("*.lean")}
jobs=int(os.environ.get("CUBE_JOBS","4"))
# Lean's prefix lookup stops at the first package directory. The support mount
# already owns IEANTN/ and LeanCert/, but not these baseline modules. Relocate
# ONLY module names/import header entries; declarations and proofs are unchanged.
for old in ORIG.rglob('*.lean'):
    q=old.relative_to(ORIG)
    if q.parts[0] in ('IEANTN','LeanCert'):
        q=Path('CubeStudyDeps')/q
    new=SRC/q
    text=re.sub(r'(?m)^(\s*(?:public |private |meta )?import\s+)(IEANTN|LeanCert)(?=\.)',
                r'\1CubeStudyDeps.\2',old.read_text())
    if not new.exists() or new.read_text()!=text:
        new.parent.mkdir(parents=True,exist_ok=True)
        new.write_text(text)

roots=sys.argv[1:] or ["CubeWide","CubeSecondary","DualAudit"]
def rel(n, ext):
    return Path(*n.split(".")).with_suffix(ext)
def src(n):
    q=LOCAL.get(n,SRC/rel(n,'.lean'))
    return q if q.is_file() else None
def imports(p):
    ans=[]
    for line in p.read_text().splitlines():
        m=re.match(r'\s*(?:public |private |meta )?import\s+([^/]+)',line)
        if m: ans.extend(m.group(1).strip().split())
    return ans
graph={}
def visit(n):
    if n in graph or (SUP / rel(n,'.olean')).is_file() or src(n) is None: return
    graph[n]=[m for m in imports(src(n)) if src(m) and not (SUP / rel(m,'.olean')).is_file()]
    for m in graph[n]:visit(m)
for n in roots:visit(n)
print(len(graph),"source modules",flush=True)
LOG.mkdir(exist_ok=True)
def build(n):
    p=src(n)
    o=OUT/rel(n,'.olean')
    if o.is_file() and o.stat().st_mtime>=max([p.stat().st_mtime]+[(OUT/rel(m,'.olean')).stat().st_mtime for m in graph[n]]):
        return True
    o.parent.mkdir(parents=True,exist_ok=True)
    with (LOG/(n+'.log')).open('w') as f:
        if o.exists():o.unlink()
        print("start", n, flush=True)
        r=subprocess.run(['/bin/lean','--root='+str(p.parent if n in LOCAL else SRC),'-o',str(o),str(p)],cwd='/work',stdout=f,stderr=subprocess.STDOUT)
        print("finish", n, r.returncode, flush=True)
        return r.returncode==0
with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
    rest=set(graph); done=set(); cur={}
    while rest or cur:
        for n in list(sorted(rest)):
            if len(cur)>=jobs:break
            if set(graph[n])<=done:
                cur[ex.submit(build,n)]=n;rest.remove(n)
        if not cur:
            if rest:raise SystemExit("unsatisfied dependencies: "+str(rest))
            break
        for f in cf.wait(cur,return_when=cf.FIRST_COMPLETED).done:
            n=cur.pop(f)
            if not f.result():raise SystemExit("failed "+n+"; see "+str(LOG/(n+'.log')))
            done.add(n)
