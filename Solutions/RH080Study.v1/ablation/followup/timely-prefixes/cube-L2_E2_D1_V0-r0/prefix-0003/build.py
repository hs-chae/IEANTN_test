"""Rebuild only assigned baseline imports and selected local modules via /bin/lean."""
from pathlib import Path as P
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import os, subprocess, sys, re
work=P("/work")
base=P("/representation/source")
args=sys.argv[1:]
if "--isolate-lean-cert" in args:
    # /bin/lean searches /source_pv/objects first. Its partial LeanCert
    # directory shadows the baseline LeanCert package. Copy and rename the
    # entire baseline LeanCert prefix in scratch, including qualified names;
    # do not touch source mounts or the preloaded modules.
    args.remove("--isolate-lean-cert")
    scratch=work/"octicsrc"
    for p in base.rglob("*.lean"):
        pp=scratch / str(p.relative_to(base)).replace("LeanCert","CubeLeanCert")
        pp.parent.mkdir(parents=True,exist_ok=True)
        pp.write_text(re.sub(r"\bLeanCert\b","CubeLeanCert",p.read_text()))
    base=scratch
local=P(__file__).resolve().parent
out=work/"objects"
out.mkdir(exist_ok=True)
logs=work/"buildlogs"
logs.mkdir(exist_ok=True)
roots=["/source_pv/objects"]+["/generic/lib/"+x for x in
    ("mathlib","plausible","LeanSearchClient","importGraph","proofwidgets","aesop","Qq","batteries")]
deps={}
src={}
def register(mod):
    p=P(mod.replace(".","/")+".lean")
    if (out/p.with_suffix(".olean")).exists(): return
    if any((P(r)/p.with_suffix(".olean")).exists() for r in roots): return
    if mod.startswith(("Lean.","Init.","Std.")) or mod in ("Lean","Init","Std"): return
    if mod in deps: return
    src[mod]=local/p if (local/p).exists() else base/p
    s=src[mod].read_text()
    deps[mod]=[i for l in s.splitlines() if l.startswith("import ")
               for i in l.split("--",1)[0].split()[1:]]
    for i in deps[mod]: register(i)
for m in args: register(m)
def build(m):
    p=out/P(m.replace(".","/")+".olean")
    p.parent.mkdir(parents=True,exist_ok=True)
    lf=logs/(m+".log")
    with lf.open("w") as f:
        rv=subprocess.run(["/bin/lean","-o",str(p),str(src[m])],cwd=src[m].parent,
                          stdout=f,stderr=subprocess.STDOUT)
    if rv.returncode:
        p.unlink(missing_ok=True)
        raise RuntimeError(m+" : "+lf.read_text()[-5000:])
    return m
print("build closure:",len(deps),flush=True)
done=set()
with ThreadPoolExecutor(max_workers=int(os.environ.get("CUBE_BUILD_J","2"))) as pool:
    pending={}
    unscheduled=set(deps)
    while pending or unscheduled:
        for m in sorted(unscheduled):
            if len(pending)>=int(os.environ.get("CUBE_BUILD_J","2")): break
            if all(d not in deps or d in done for d in deps[m]):
                pending[pool.submit(build,m)]=m
                unscheduled.remove(m)
        if not pending: raise RuntimeError("cycle or missing dependency")
        for p in wait(pending,return_when=FIRST_COMPLETED)[0]:
            m=p.result()
            done.add(m)
            del pending[p]
            print("built",m,flush=True)
