#!/usr/bin/env python3
"""Actual positive and rejection CLIs in default/-O/-OO; explicit checks."""
from pathlib import Path
import copy,hashlib,json,subprocess,sys,zipfile
R=Path(__file__).resolve().parents[1];SCRIPT=R/'network/Solutions/RHExposureStudy.v1/scripts/restore_evidence_bundle.py';D=Path('/data/ivy-rh-propagation-20261120/bundle-cli-controls-v2')
if D.exists():raise ValueError('fresh control directory required')
D.mkdir();script=SCRIPT.read_bytes();h=lambda b:hashlib.sha256(b).hexdigest();payload=b'mathematical reproduction fixture\n';key=h(payload);base={'schema':'RH_CONTENT_ADDRESSED_EVIDENCE_V1','restore_sha256':h(script),'files':[{'path':'proof/source.lean','sha256':key,'bytes':len(payload)}]}
cases=['positive','tampered-object','unsafe-path','boolean-bytes','nonfinite-JSON','duplicate-JSON-key','missing-object','extra-object','duplicate-physical-member','wrong-restorer','conflicting-size','duplicate-logical-path']
archives={}
for label in cases:
 m=copy.deepcopy(base);objects={'objects/'+key:payload}
 if label=='tampered-object':objects['objects/'+key]=b'wrong'
 if label=='unsafe-path':m['files'][0]['path']='../outside.lean'
 if label=='boolean-bytes':m['files'][0]['bytes']=True
 if label=='missing-object':objects={}
 if label=='extra-object':objects['objects/'+h(b'extra')]=b'extra'
 if label=='wrong-restorer':m['restore_sha256']='0'*64
 if label=='conflicting-size':m['files'].append(dict(m['files'][0],path='another.lean',bytes=123))
 if label=='duplicate-logical-path':m['files'].append(dict(m['files'][0]))
 raw=json.dumps(m).encode()
 if label=='nonfinite-JSON':raw=raw[:-1]+b',"overflow":1e999}'
 if label=='duplicate-JSON-key':raw=raw[:-1]+b',"schema":"RH_CONTENT_ADDRESSED_EVIDENCE_V1"}'
 p=D/(label+'.zip')
 with zipfile.ZipFile(p,'w',zipfile.ZIP_DEFLATED)as z:
  z.writestr('MANIFEST.json',raw);z.writestr('RESTORE.py',script);z.writestr('README.txt','fixture')
  for k,v in objects.items():z.writestr(k,v)
  if label=='duplicate-physical-member':z.writestr('README.txt','duplicate')
 archives[label]=p
rows=[]
for mode,args in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
 for label,p in archives.items():
  out=D/(mode+'-'+label);cmd=[sys.executable,*args,str(SCRIPT),str(p),'--out',str(out)];r=subprocess.run(cmd,capture_output=True,text=True);good=(r.returncode==0)if label=='positive'else(r.returncode!=0)
  if not good:raise ValueError('acceptance control failed '+mode+' '+label)
  receipt=out.parent/(out.name+'-RESTORE_RECEIPT.json')
  if label!='positive'and receipt.exists():raise ValueError('failed control emitted acceptance')
  rows.append({'mode':mode,'case':label,'returncode':r.returncode,'passed':good,'stdout':r.stdout,'stderr':r.stderr})
(D/'RESULT.json').write_text(json.dumps({'status':'PASS_ALL_36_ACTUAL_RESTORE_CLI_CONTROLS','restorer_sha256':h(script),'test_source_sha256':h(Path(__file__).read_bytes()),'rows':rows},indent=2)+'\n');print('PASS36 actual CLIs default/O/OO')
