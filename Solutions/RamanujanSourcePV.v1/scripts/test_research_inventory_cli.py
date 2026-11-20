#!/usr/bin/env python3
"""Actual inventory acceptance/rejection controls in every Python optimization mode."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,shutil,subprocess,sys
S=Path(__file__).resolve().parents[1]
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh owned fixture output');out.mkdir(parents=True)
 collector=S/'scripts/collect_research_inventory.py';spec=importlib.util.spec_from_file_location('inventory_selection',collector);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 seed=out/'seed';(seed/'scripts').mkdir(parents=True);shutil.copy2(collector,seed/'scripts'/collector.name);(seed/'c').mkdir();
 for source in (S/'c').iterdir():
  if source.is_file():shutil.copy2(source,seed/'c'/source.name)
 context=json.loads((S/'BUILD_CONTEXT.json').read_text());original_objects=Path(context['new_application_object_root']);first=next(iter(mod.SELECTED));results=[]
 for name in mod.SELECTED:
  source=S/'RamanujanPV'/(name+'.lean');target=seed/'RamanujanPV'/source.name;target.parent.mkdir(exist_ok=True);shutil.copy2(source,target)
  candidates=[]
  for r in (S/'audit'/('RamanujanPV.'+name)).glob('*/RUN.json'):
   row=json.loads(r.read_text())
   if row.get('status')=='COMPILED' and row.get('returncode')==0 and row.get('source_sha256')==sha(source):candidates.append(r)
  need(candidates,'current actual successful source receipt');r=max(candidates,key=lambda x:int(x.parent.name));shutil.copytree(r.parent,seed/'audit'/('RamanujanPV.'+name)/r.parent.name)
  obj=seed/'objects/RamanujanPV'/(name+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(original_objects/'RamanujanPV'/(name+'.olean'),obj)
 for mode,label in [([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]:
  for case in ['valid','duplicate-json','source-drift','object-drift','snapshot-drift','native-axiom']:
   fixture=out/(label+'-'+case);shutil.copytree(seed,fixture);c=dict(context,new_application_object_root=str(fixture/'objects'));(fixture/'BUILD_CONTEXT.json').write_text(json.dumps(c));receipt=next((fixture/'audit'/('RamanujanPV.'+first)).glob('*/RUN.json'));r=json.loads(receipt.read_text())
   if case=='duplicate-json':receipt.write_text(receipt.read_text().replace('{','{"returncode":0,',1))
   elif case=='source-drift':(fixture/'RamanujanPV'/(first+'.lean')).write_text('changed source')
   elif case=='object-drift':(fixture/'objects/RamanujanPV'/(first+'.olean')).write_bytes(b'changed object')
   elif case=='snapshot-drift':(receipt.parent/'source.lean').write_text('changed snapshot')
   elif case=='native-axiom':
    log=receipt.parent/'stdout';log.write_text(log.read_text().replace('propext','Lean.ofReduceBool'));r['stdout_sha256']=sha(log);receipt.write_text(json.dumps(r))
   command=[sys.executable,*mode,str(fixture/'scripts'/collector.name),'--out',str(fixture/'ACCEPTED.json')];run=subprocess.run(command,capture_output=True,text=True);(fixture/'stdout').write_text(run.stdout);(fixture/'stderr').write_text(run.stderr);accepted=case=='valid';need((run.returncode==0)==accepted,'actual CLI verdict '+label+' '+case);need((fixture/'ACCEPTED.json').exists()==accepted,'no stale positive receipt')
   results.append({'mode':mode,'case':case,'returncode':run.returncode,'command':command,'stdout_sha256':sha(fixture/'stdout'),'stderr_sha256':sha(fixture/'stderr'),'expected_acceptance':accepted})
 result={'status':'PASS','actual_cli_controls':len(results),'collector_sha256':sha(collector),'cases':results,'optimization_modes':['normal','-O','-OO']};(out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'PASS','actual_cli_controls':len(results)}))
if __name__=='__main__':main()
