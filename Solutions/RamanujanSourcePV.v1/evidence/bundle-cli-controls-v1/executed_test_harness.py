from pathlib import Path
import subprocess,sys,json,zipfile,hashlib
r=Path(__file__).resolve().parents[1];script=r/'network/Solutions/RamanujanSourcePV.v1/scripts/package_research.py';base=r/'publication/bundle-controls';original=base/'PROTOTYPE.zip';out=base/'cli-v1'
if out.exists():raise ValueError('fresh CLI fixture directory required')
out.mkdir();cases={}
with zipfile.ZipFile(original) as z:
 for case in ['changed-payload','extra-member','false-completion','duplicate-json']:
  p=out/(case+'.zip')
  with zipfile.ZipFile(p,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=1) as target:
   for name in z.namelist():
    data=z.read(name)
    if name=='START_HERE.txt' and case=='changed-payload':data+=b'changed'
    if name=='MANIFEST.json':
     if case=='false-completion':
      d=json.loads(data);d['complete_all_real_target']=True;data=json.dumps(d).encode()
     if case=='duplicate-json':data=data.replace(b'{',b'{"schema":"duplicate",',1)
    target.writestr(name,data)
   if case=='extra-member':target.writestr('EXTRA.txt','extra')
  cases[case]=p
results=[]
for mode in [[],['-O'],['-OO']]:
 for case,path in [('valid',original),*cases.items()]:
  cmd=[sys.executable,*mode,str(script),'--check',str(path)];run=subprocess.run(cmd,capture_output=True,text=True);expected=case=='valid'
  if (run.returncode==0)!=expected:raise ValueError('actual CLI verdict mismatch '+str((mode,case)))
  results.append(dict(mode=mode,case=case,returncode=run.returncode,expected_acceptance=expected,stdout_sha256=hashlib.sha256(run.stdout.encode()).hexdigest(),stderr_sha256=hashlib.sha256(run.stderr.encode()).hexdigest()))
result=dict(status='ALL_ACTUAL_BUNDLE_CLI_CONTROLS_PASS',controls=len(results),validator_sha256=hashlib.sha256(script.read_bytes()).hexdigest(),original_archive_sha256=hashlib.sha256(original.read_bytes()).hexdigest(),cases=results)
(out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='cases'}))
