from pathlib import Path
import argparse,json,os,subprocess,time,hashlib,sys
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('module');a=p.parse_args()
s=Path(__file__).resolve().parent;d=Path('/data/ivy-rh-continuation-20261122/ramanujan/dev');d.mkdir(parents=True,exist_ok=True)
ctx=json.loads((s.parent/'scripts/GENERIC_CONTEXT.json').read_text())
bank=Path('/data/ivy-rh-continuation-20261122/ramanujan/fresh-base-v1/objects')
attempt=d/(a.module+'-attempt-'+str(time.time_ns()));(attempt/'source').mkdir(parents=True)
f=s/(a.module+'.lean');raw=f.read_bytes();frozen=attempt/'source'/f.name;frozen.write_bytes(raw)
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(d),'/data/ivy-rh-continuation-20261122/ramanujan/source-component-v1/union',str(bank),*ctx['generic_libraries']]);start=time.monotonic()
r=subprocess.run(['/usr/bin/time','-v',ctx['compiler'],'--root='+str(attempt/'source'),'-o',str(d/(a.module+'.olean')),str(frozen)],cwd=attempt/'source',env=env,text=True,capture_output=True)
(attempt/'stdout.txt').write_text(r.stdout);(attempt/'stderr.txt').write_text(r.stderr)
(d/(a.module+'.stdout')).write_text(r.stdout);(d/(a.module+'.stderr')).write_text(r.stderr)
receipt={'status':'PASS'if r.returncode==0 else'FAIL','returncode':r.returncode,'module':a.module,'source_sha256':hashlib.sha256(raw).hexdigest(),'source_frozen':str(frozen),'compiler_sha256':ctx['compiler_sha256'],'development_import_bank':str(bank),'seconds':time.monotonic()-start,'source_unchanged_during_build':raw==f.read_bytes()}
(attempt/'RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n');(d/(a.module+'.json')).write_text(json.dumps(receipt,indent=2)+'\n');print('\n'.join(line for line in r.stdout.splitlines()if 'error' in line or 'depends on axioms' in line)[:7000]);print(r.stderr[-300:]if r.returncode else'');print(json.dumps(receipt));sys.exit(r.returncode)
