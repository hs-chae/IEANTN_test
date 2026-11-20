from pathlib import Path
import gzip,hashlib,io,json,subprocess,sys,tarfile,zipfile
r=Path(__file__).resolve().parents[1];script=r/'network/Solutions/RamanujanSourcePV.v1/scripts/package_research.py';base=r/'publication/bundle-controls';out=base/'all-formats-v2'
if out.exists():raise ValueError('fresh actual CLI control directory')
out.mkdir();results=[]
def write(path,kind,payloads,symlink=False):
 if kind=='zip':
  with zipfile.ZipFile(path,'w',compression=zipfile.ZIP_DEFLATED) as z:
   for name,data in payloads.items():
    info=zipfile.ZipInfo(name);info.external_attr=(0o120777 if symlink and name=='payload.txt' else 0o100644)<<16;z.writestr(info,data)
 else:
  with tarfile.open(path,'w:gz') as z:
   for name,data in payloads.items():
    info=tarfile.TarInfo(name);info.size=len(data)
    if symlink and name=='payload.txt':info.type=tarfile.SYMTYPE;info.linkname='elsewhere';info.size=0;z.addfile(info)
    else:z.addfile(info,io.BytesIO(data))
for kind,prototype,ext in [('zip',base/'PROTOTYPE.zip','.zip'),('tar.gz',base/'PROTOTYPE-v2.tar.gz','.tar.gz')]:
 cases={}
 for case in ['changed-payload','extra-member','false-completion','duplicate-json','symlink-member','absolute-member']:
  payload=b'actual data';manifest=dict(schema='RAMANUJAN_COMMITTED_RESEARCH_BUNDLE_V1',complete_all_real_target=False,commit='0664c1e7c723a372403a95eeb3ba2d94b04ff3e8',files=[dict(path='payload.txt',bytes=len(payload),sha256=hashlib.sha256(payload).hexdigest())]);data={'payload.txt':payload}
  if case=='changed-payload':data['payload.txt']+=b'changed'
  if case=='extra-member':data['extra.txt']=b'extra'
  if case=='false-completion':manifest['complete_all_real_target']=True
  if case=='absolute-member':data['/absolute.txt']=b'bad'
  encoded=json.dumps(manifest).encode()
  if case=='duplicate-json':encoded=encoded.replace(b'{',b'{"schema":"duplicate",',1)
  data['MANIFEST.json']=encoded;p=out/(kind.replace('.','-')+'-'+case+ext);write(p,kind,data,case=='symlink-member');cases[case]=p
 for mode in [[],['-O'],['-OO']]:
  for case,file in [('valid',prototype),*cases.items()]:
   command=[sys.executable,*mode,str(script),'--check',str(file)];proc=subprocess.run(command,capture_output=True);expected=case=='valid'
   if (proc.returncode==0)!=expected:raise ValueError('actual CLI outcome '+str((kind,mode,case)))
   results.append(dict(format=kind,mode=mode,case=case,returncode=proc.returncode,expected_acceptance=expected,stdout_sha256=hashlib.sha256(proc.stdout).hexdigest(),stderr_sha256=hashlib.sha256(proc.stderr).hexdigest()))
receipt=dict(status='BOTH_ARCHIVE_FORMATS_ALL42_ACTUAL_CLI_CONTROLS_PASS',validator_sha256=hashlib.sha256(script.read_bytes()).hexdigest(),controls=len(results),cases=results)
(out/'RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k!='cases'}))
