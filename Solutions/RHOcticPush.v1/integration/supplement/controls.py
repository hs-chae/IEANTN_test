#!/usr/bin/env python3
"""Exercise actual supplemental validator CLI in normal/-O/-OO modes.
Mutations affect only a fresh experiment-owned copy, never accepted evidence.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys
HERE=Path(__file__).resolve().parent
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();out=a.out.resolve();need(not out.exists(),'fresh control output required');out.mkdir(parents=True);clone=out/'mutant';shutil.copytree(a.run.resolve(),clone,symlinks=True);records=[]
 def cli(name,want):
  for opts in [[],['-O'],['-OO']]:
   cmd=[sys.executable,*opts,str(HERE/'reproduce.py'),'--verify',str(clone)];cp=subprocess.run(cmd,text=True,capture_output=True);key=str(len(records))+'-'+name+'-O'+str(len(opts)and len(opts[0])-1);(out/(key+'.stdout')).write_text(cp.stdout);(out/(key+'.stderr')).write_text(cp.stderr);need((cp.returncode==0)==want,'unexpected actual validator outcome:'+key);records.append({'name':name,'optimization':opts,'command':cmd,'returncode':cp.returncode,'expected_accept':want,'stdout_sha256':sha(out/(key+'.stdout')),'stderr_sha256':sha(out/(key+'.stderr'))})
 cli('clean-relocated-copy',True);rr=json.loads((clone/'RESULT.json').read_text());m=json.loads((clone/'SOURCE_CLOSURE.executed.json').read_text());mod=m['modules'][0]['module'];rel=mod.replace('.','/');targets=[clone/'source'/(rel+'.lean'),clone/'objects'/(rel+'.olean'),clone/'logs'/(mod+'.stdout'),clone/'logs'/(mod+'.stderr'),clone/'reproduce.executed.py',clone/'SOURCE_CLOSURE.executed.json',clone/'TREE_RSS.csv']
 for target in targets:
  need(target.resolve().is_relative_to(clone)and not target.is_symlink(),'mutation escapes experiment-owned copy');old=target.read_bytes();target.write_bytes(old+b'\nMUTATION\n')
  try:cli('byte-'+target.name,False)
  finally:target.write_bytes(old)
 original=(clone/'RESULT.json').read_bytes()
 mutations=['missing-probe','bool-probe-status','nonzero-probe','wrong-probe-command','foreign-app-dependency','false-PV-label','incomplete-module-count']
 for case in mutations:
  r=json.loads(original);restore=None
  if case=='missing-probe':r['dependency_probes'].pop()
  elif case=='bool-probe-status':r['dependency_probes'][0]['returncode']=False
  elif case=='nonzero-probe':r['dependency_probes'][0]['returncode']=1
  elif case=='wrong-probe-command':r['dependency_probes'][0]['command']=['false']
  elif case=='false-PV-label':r['whole_pipeline_source_first_PV']=True
  elif case=='incomplete-module-count':r['new_modules']-=1
  else:
   q=r['dependency_probes'][0];p=clone/'dependencies'/q['stdout'];restore=(p,p.read_bytes());p.write_bytes(p.read_bytes()+b'/tmp/foreign-application.olean\n');q['stdout_sha256']=sha(p)
  (clone/'RESULT.json').write_text(json.dumps(r,indent=2)+'\n')
  try:cli(case,False)
  finally:
   (clone/'RESULT.json').write_bytes(original)
   if restore:restore[0].write_bytes(restore[1])
 cli('restored',True);receipt={'status':'PASS_ACTUAL_SUPPLEMENT_CLI_CONTROLS_ALL_MODES','cases':len(records),'controller_sha256':sha(HERE/'reproduce.py'),'control_source_sha256':sha(Path(__file__)),'accepted_run_RESULT_sha256':sha(a.run/'RESULT.json'),'records':records};pending=out/'CANDIDATE.json';pending.write_text(json.dumps(receipt,indent=2)+'\n');os.replace(pending,out/'RESULT.json');print(receipt['status'],len(records))
if __name__=='__main__':main()
