#!/usr/bin/env python3
"""Actual CLI acceptance/rejection checks in every Python optimization mode."""
from pathlib import Path
import argparse,json,os,shutil,subprocess,sys,time
from reproduce_cold_append import need,read,sha,save
B=Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--basis',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--resource-proof',type=Path);a=p.parse_args();basis=a.basis.resolve();out=a.out.resolve()
 need(not out.exists(),'fresh controls output');need((basis/'RESULT.json').is_file(),'completed original basis required')
 out.mkdir(parents=True);validator_hash=sha(B/'reproduce_cold_append.py');controller_hash=sha(__file__);before=sha(basis/'RESULT.json');build=read(basis/'BUILD.json');first=build['modules'][0]['module'].replace('.','/')
 # Private byte copies only; never hard-link or modify the original basis.
 clones={}
 for kind in ['bad-source','bad-object','bad-json','boolean-returncode']:
  dest=out/(kind+'-basis');shutil.copytree(basis,dest);(dest/'EXPERIMENT_OWNED_COPY').write_text('regenerable private negative control\n')
  if kind=='bad-source':
   q=dest/'source'/(first+'.lean');q.write_bytes(q.read_bytes()+b'\n-- intentional reproducibility control\n')
  elif kind=='bad-object':
   q=dest/'objects'/(first+'.olean');q.write_bytes(q.read_bytes()+b'\0')
  elif kind=='boolean-returncode':
   q=dest/'BUILD.json';j=read(q);j['modules'][0]['returncode']=False;q.write_text(json.dumps(j,indent=2)+'\n')
   q=dest/'RESULT.json';j=read(q);j['BUILD_sha256']=sha(dest/'BUILD.json');q.write_text(json.dumps(j,indent=2)+'\n')
  else:
   q=dest/'RESULT.json';s=q.read_text();q.write_text(s.replace('{','{"status":"duplicate-control",',1))
  clones[kind]=dest
 rows=[];start=time.monotonic()
 for flag in ['', '-O','-OO']:
  mode=flag or 'normal'
  for name,root,expect in [('accepted',basis,None),('bad-source',clones['bad-source'],'basis source:'),('bad-object',clones['bad-object'],'basis object:'),('bad-json',clones['bad-json'],'duplicate JSON key'),('boolean-returncode',clones['boolean-returncode'],'basis returncode type/status')]:
   cmd=[sys.executable,*([flag]if flag else[]),str(B/'reproduce_cold_append.py'),'--basis',str(root),'--out',str(out/(mode+'-'+name+'-unused')),'--check']
   if a.resource_proof:cmd+=['--resource-proof',str(a.resource_proof.resolve())]
   cp=subprocess.run(cmd,text=True,capture_output=True);log=out/(mode+'-'+name+'.log');log.write_text(cp.stdout+'\n'+cp.stderr)
   if expect is None:need(cp.returncode==0 and 'PASS_COMPLETE_COLD261_BASIS_AND_EXACT55_SOURCE_PREFLIGHT'in cp.stdout,'positive route failed')
   else:need(cp.returncode!=0 and expect in cp.stderr,'negative route not rejected precisely:'+name)
   rows.append({'optimization':mode,'route':name,'returncode':cp.returncode,'expected':expect or 'PASS','command':cmd,'log_sha256':sha(log)})
 need(sha(basis/'RESULT.json')==before,'original basis changed')
 need(sha(B/'reproduce_cold_append.py')==validator_hash and sha(__file__)==controller_hash,'control/validator source changed')
 save(out/'CONTROLS.json',{'controller_sha256':controller_hash,'validator_sha256':validator_hash,'status':'PASS_ALL15_ACTUAL_CLI_ROUTES','rows':rows,'seconds':time.monotonic()-start,'original_basis_RESULT_sha256':before,'cleanup':'Private copiedbasis directories checked below thenremoved; originalcompletedbasis and exactmutation recipe retained.'})
 # Preview and verify experiment ownership before deterministic temporary cleanup.
 preview=[{'path':str(x),'bytes':sum(p.stat().st_size for p in x.rglob('*')if p.is_file())}for x in clones.values()]
 save(out/'CLEANUP_PREVIEW.json',preview)
 for root in clones.values():
  need(root.is_relative_to(out)and root.name in {'bad-source-basis','bad-object-basis','bad-json-basis','boolean-returncode-basis'},'cleanup scope')
  need((root/'EXPERIMENT_OWNED_COPY').read_text()=='regenerable private negative control\n','cleanup ownership')
  shutil.rmtree(root)
 need(sha(basis/'RESULT.json')==before,'original basis changed during cleanup')
 save(out/'CLEANUP.json',{'status':'PASS_VERIFIED_REGENERABLE_PRIVATE_COPIES_REMOVED','targets':preview,'original_basis_preserved':sha(basis/'RESULT.json')==before})
 save(out/'RESULT.json',{'status':'PASS_ALL15_ACTUAL_CLI_ROUTES_AND_SCOPED_CLEANUP','controller_sha256':controller_hash,'validator_sha256':validator_hash,'CONTROLS_sha256':sha(out/'CONTROLS.json'),'CLEANUP_sha256':sha(out/'CLEANUP.json'),'original_basis_RESULT_sha256':before})
 print('PASS_ALL15_ACTUAL_CLI_ROUTES_AND_SCOPED_CLEANUP')
if __name__=='__main__':main()
