#!/usr/bin/env python3
"""Actual parser/range rejections only; no renaming/resource child launches."""
from pathlib import Path
import hashlib,json,os,subprocess,tempfile
L=Path(__file__).resolve().parent;H=L/'network/Solutions/RH080Next.v1/reproduction';G=H/'bootstrap_quiescent_resource_guard_v4.py';OUT=L/'guard-v4-cli-boundaries-v1';OUT.mkdir()
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
 for label,args in [('missing',[]),('zero',['0']),('above7200',['7201']),('fraction',['1200.5']),('noninteger',['false'])]:
  d=OUT/(mode+'-'+label);d.mkdir();cmd=['/usr/bin/python3']+flags+[str(G),'--root',str(d),'--workspace',str(d/'workspace'),'--command',str(d/'command.json'),'--receipt',str(d/'RESOURCE.json'),'--live',str(d/'LIVE.json'),'--deadline-seconds']+args
  r=subprocess.run(cmd,capture_output=True,timeout=10,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'));(d/'stdout').write_bytes(r.stdout);(d/'stderr').write_bytes(r.stderr)
  need(r.returncode!=0 and not(d/'RESOURCE.json').exists()and not(d/'workspace').exists(),'Boundary input accepted or child state created')
  need(b'Bounded deadline/sample interval required'in r.stderr or b'argument --deadline-seconds:'in r.stderr,'Failure did not reach requested argument boundary')
  rows.append(dict(mode=mode,case=label,command=cmd,returncode=r.returncode,stdout_sha256=sha(d/'stdout'),stderr_sha256=sha(d/'stderr')))
result=dict(status='PASS_PRIVATE_GUARD_V4_ALL_MODE_CLI_BOUNDARIES_NOT_REAL_RENAMING_CONTROLS',negative_cases=15,records=rows,source_sha256=sha(G),no_child_launched=True,production_fetch_executed=False)
fd,tmp=tempfile.mkstemp(dir=OUT)
with os.fdopen(fd,'w')as f:json.dump(result,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
os.link(tmp,OUT/'RESULT.json');os.unlink(tmp)
print(json.dumps({k:result[k]for k in ['status','negative_cases','source_sha256','no_child_launched']}))
