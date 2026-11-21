#!/usr/bin/env python3
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time,re
B=Path(__file__).resolve().parent;p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('module');p.add_argument('--attempt',required=True);a=p.parse_args();
if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',a.module)is None:raise RuntimeError('strict Lean module identifier')
if re.fullmatch(r'[A-Za-z0-9_.-]+',a.attempt)is None or '..'in a.attempt:raise RuntimeError('strict owned attempt identifier')
c=json.loads((B/'BUILD_CONTEXT.json').read_text());o=B/'objects';o.mkdir(exist_ok=True);src=B/(a.module.replace('.','/')+'.lean');d=B/'compile-observations'/a.attempt;d.mkdir(parents=True,exist_ok=False)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
if sha(c['compiler'])!=c['compiler_sha256']:raise RuntimeError('compiler pin')
obj=o/(a.module.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
cmd=[c['compiler'],'-R',str(B),'-o',str(o/(a.module.replace('.','/')+'.olean')),str(src)];before=sha(src);t=time.monotonic();r=subprocess.run(cmd,cwd=B,env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(o),*c['generic_libraries']])),capture_output=True,text=True);(d/'stdout').write_text(r.stdout);(d/'stderr').write_text(r.stderr);(d/'source.lean').write_bytes(src.read_bytes());(d/'OBSERVATION.json').write_text(json.dumps({'module':a.module,'command':cmd,'exit_code':r.returncode,'elapsed_seconds':time.monotonic()-t,'source_sha256':before,'source_unchanged':sha(src)==before,'compiler_sha256':sha(c['compiler']),'not_source_first_PV':True,'not_Comparator_receipt':True},indent=2)+'\n');print(r.stdout[:13000]+r.stderr[:1000]);print('EXIT',r.returncode);raise SystemExit(r.returncode if sha(src)==before else 1)
