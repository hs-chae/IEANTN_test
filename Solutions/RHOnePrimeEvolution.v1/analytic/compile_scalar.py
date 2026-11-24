#!/usr/bin/env python3
"""Compile only the scalar CMS frontend; this does not establish an RH theorem."""
from pathlib import Path
import argparse,hashlib,json,os,resource,subprocess,time
p=argparse.ArgumentParser(allow_abbrev=False)
p.add_argument('--context',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
p.add_argument('--module',default='CMSScalarFrontier')
p.add_argument('--prior-objects',type=Path)
a=p.parse_args(); b=Path(__file__).resolve().parent
if a.out.exists(): raise SystemExit('Output must be a fresh directory')
a.out.mkdir(parents=True)
c=json.loads(a.context.read_text());env=os.environ.copy()
env['LEAN_PATH']=':'.join(([str(a.prior_objects)] if a.prior_objects else [])+c['generic_libraries']);env['LEAN_NUM_THREADS']='2'
src=b/(a.module+'.lean');cmd=[c['compiler'],'-j2','--root='+str(b),'-o',str(a.out/(a.module+'.olean')),str(src)]
(a.out/'source.lean').write_bytes(src.read_bytes())
(a.out/'compiler-script.py').write_bytes(Path(__file__).read_bytes())
t=time.monotonic()
r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=b,env=env,text=True,capture_output=True,
 preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3)))
(a.out/'stdout').write_text(r.stdout);(a.out/'stderr').write_text(r.stderr)
rec={'status':'COMPILED_SCOPED_MODULE_USING_PINNED_PREDECESSOR_OBJECTS'if r.returncode==0 else'FAIL','returncode':r.returncode,
'seconds':time.monotonic()-t,'command':cmd,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
'compiler_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'LEAN_PATH':env['LEAN_PATH'],
'scope':{'module':a.module,'formal_source_claims':'Inspect exact theorem statements and source predicates; this script reports compilation only','source_first_PV':False,'fresh_transitive_rebuild':False}}
(a.out/'RUN.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({'status':rec['status'],'seconds':rec['seconds']}));print(r.stdout)
raise SystemExit(r.returncode)
