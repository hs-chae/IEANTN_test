from pathlib import Path
import subprocess as sp, json, sys, hashlib, os, time, shlex
from concurrent.futures import ThreadPoolExecutor
P='/usr/bin/python3.10'; G='/usr/bin/g++'
root=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/work/independent_replay')
root.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def go(cmds,cwd):
    z=[]
    for argv in cmds:
        t=time.monotonic()
        r=sp.run(argv,cwd=cwd,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',LC_ALL='C'),capture_output=True)
        z.append(dict(argv=argv,cwd=str(cwd),status=r.returncode,stdout=r.stdout.decode(),stderr=r.stderr.decode(),stdout_sha256=hashlib.sha256(r.stdout).hexdigest(),seconds=round(time.monotonic()-t,3)))
        if r.returncode:break
    return z
c=root/'candidate'
rr=go([[P,'/task/RESTORE_CANDIDATE.py','--out',str(c)],[P,'--version'],[G,'--version']],root)
for r in rr:print(r,flush=True)
if any(r['status'] for r in rr):sys.exit(1)
idx=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
src=json.loads(Path('/task/SOURCE_INDEX.json').read_text())
for r in idx['candidate_files']:assert sha(c/r['original_name'])==r['sha256']
for r in src['sources']:
    for k in ['pdf','text']:assert sha(Path(src['root'])/r[k])==r[k+'_sha256']
rr=go([[G,'-std=c++17','-O3','small_end.cpp','-o','/work/small_end']],c)
for r in rr:print(r,flush=True)
jobs=[]
for f,n,flags in [('finite','finite',['-O3']),('finite','finite_ubsan',['-O2','-fsanitize=undefined','-fno-sanitize-recover=undefined']),('finite_trials','finite_trials',['-O3']),('finite_frontier','frontier',['-O3']),('finite_frontier','frontier_ubsan',['-O2','-fsanitize=undefined','-fno-sanitize-recover=undefined'])]:
    exe=str(root/n)
    jobs.append((n+'_evidence.txt',[[G,'-std=c++17',*flags,f+'.cpp','-o',exe],[exe]]))
for f,n,options in [('check','gap',[[]]),('check','gap_basic',[['--basic']]),('mertens_check','mertens',[[],['--basic']]),('repair_check','repair_gap',[[]]),('repair_check','repair_gap_basic',[['--basic']]),('repair_mertens','repair_mertens',[[]]),('source_audit','source_audit',[[]])]:
    jobs.append((n+'_evidence.txt',[[P,f+'.py',*args] for args in options]))
jobs.append((None,[['/work/small_end','38358837677','38358837682','38358837683','14111427770'],[P,'-c',"import check; N=38358837682; x=check.I(N)+check.I('.1'); print(check.I(1).exp()*x*632207037/x.ln()-1644673232**2)"]]))
def job(item):
    n,cmds=item
    rows=go(cmds,c)
    out=''.join(r['stdout'] for r in rows).encode()
    return dict(receipt=n,expected_sha256=sha(c/n) if n else None,byte_match=out==(c/n).read_bytes() if n else None,commands=rows)
with ThreadPoolExecutor(max_workers=3) as pool:
    for j in pool.map(job,jobs):print(json.dumps(j),flush=True)
